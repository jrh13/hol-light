(* ========================================================================= *)
(* HILBERT-WARING THEOREM.                                                   *)
(*                                                                           *)
(*   |- !e. 1 <= e ==> ?k. !n. ?f. n = nsum(1..k) (\i. f i EXP e)            *)
(*                                                                           *)
(* Every natural number is a sum of a bounded number k(e) of e-th powers.    *)
(* Proof: Linnik's elementary method (Khinchin, "Three Pearls of Number      *)
(* Theory", Ch.3): the scale-uniform fiber-count induction DPWIH2 gives the  *)
(* Fundamental Lemma FUND_LEMMA_CF, then Schnirelmann's density-to-basis     *)
(* theorem turns the resulting positive lower density into a finite basis.   *)
(*                                                                           *)
(* Layout: the proof is organised into the sections below (Khinchin's Lemmas *)
(* 2-5, the difference-polynomial fiber induction, and the Schnirelmann      *)
(* capstone).                                                                *)
(* ========================================================================= *)

needs "Library/isum.ml";;
needs "Library/permutations.ml";;
needs "Examples/schnirelmann.ml";;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* Khinchin Sec.3 foundation: integer interval / linear-count lemmas         *)
(* ------------------------------------------------------------------------- *)

let INT_INTERVAL_IMAGE = prove
 (`!lo hi:int. lo <= hi
               ==> {k:int | lo <= k /\ k <= hi} =
                   IMAGE (\j. lo + &j) (0..num_of_int(hi - lo))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&(num_of_int(hi - lo)) = hi - lo` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `k:int` THEN EQ_TAC THEN STRIP_TAC THENL
   [EXISTS_TAC `num_of_int(k - lo)` THEN
    SUBGOAL_THEN `&(num_of_int(k - lo)) = k - lo` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_INT_ARITH_TAC;
      CONJ_TAC THENL
       [ARITH_TAC;
        REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
        ASM_INT_ARITH_TAC]];
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[GSYM INT_OF_NUM_LE]) THEN
    ASM_INT_ARITH_TAC]);;

let EXACT_INT_INTERVAL_CARD = prove
 (`!lo hi:int. lo <= hi ==> CARD {k:int | lo <= k /\
  k <= hi} = num_of_int(hi - lo + &1)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[INT_INTERVAL_IMAGE] THEN
  SUBGOAL_THEN `CARD(IMAGE (\j. lo + &j) (0..num_of_int(hi - lo))) =
                CARD(0..num_of_int(hi - lo))` SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CARD_NUMSEG; SUB_0] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
  SUBGOAL_THEN `&(num_of_int(hi - lo)):int = hi - lo` SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int(hi - lo + &1)):int = hi - lo + &1`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  INT_ARITH_TAC);;

let INT_INTERVAL_CARD_LE = prove
 (`!lo hi:int. lo <= hi
               ==> CARD {k:int | lo <= k /\ k <= hi}
                   <= num_of_int(hi - lo + &1)`,
  SIMP_TAC[EXACT_INT_INTERVAL_CARD; LE_REFL]);;

let KQ_UB = prove
 (`!k q B:int. &1 <= q /\ k * q <= B /\ &0 <= B ==> k <= B`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(INT_ARITH `(k:int) <= &0 \/ &0 < k`) THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `k * q:int` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_RID] THEN
  MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC);;

let KQ_LB = prove
 (`!k q C:int. &1 <= q /\ C <= k * q /\ C <= &0 ==> C <= k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`--k:int`; `q:int`; `--C:int`] KQ_UB) THEN
  REWRITE_TAC[GSYM INT_MUL_LNEG] THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Khinchin Sec.3: arithmetic-progression and divisibility lemmas            *)
(* ------------------------------------------------------------------------- *)

let INT_FINITE_MAX_ELEMENT = prove
 (`!s:int->bool. FINITE s /\ ~(s = {})
                 ==> ?M:int. M IN s /\ (!x. x IN s ==> x <= M)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:int->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; UNWIND_THM2; INT_LE_REFL] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  MESON_TAC[INT_LE_TOTAL; INT_LE_REFL; INT_LE_TRANS]);;

let INT_FINITE_MIN_ELEMENT = prove
 (`!s:int->bool. FINITE s /\ ~(s = {})
                 ==> ?N:int. N IN s /\ (!x. x IN s ==> N <= x)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; IN_INSERT] THEN REPEAT GEN_TAC THEN
  ASM_CASES_TAC `s:int->bool = {}` THEN
  ASM_SIMP_TAC[NOT_IN_EMPTY; UNWIND_THM2; INT_LE_REFL] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  MESON_TAC[INT_LE_TOTAL; INT_LE_REFL; INT_LE_TRANS]);;

let INT_LE_RMUL_CANCEL = prove
 (`!a b q:int. &1 <= q /\ a * q <= b * q ==> a <= b`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`(a - b):int`; `q:int`; `&0:int`] KQ_UB) THEN
  REWRITE_TAC[INT_SUB_RDISTRIB] THEN ANTS_TAC THENL
   [ASM_INT_ARITH_TAC; INT_ARITH_TAC]);;

let AP_SUBSET_IMAGE = prove
 (`!S q N M A:int r.
      &1 <= q /\ &0 <= A /\ q divides (M - N) /\ N <= M /\
      (!x. x IN S ==> N <= x /\ x <= M /\ q divides (x - r)) /\
       q divides (N - r)
      ==> S SUBSET IMAGE (\k:int. N + k * q) {k:int | &0 <= k /\
       k <= (M - N) div q}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `z:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `z:int` th)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q:int) divides (z - N)` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC 
     [`(q:int) divides (z - r)`; `(q:int) divides (N - r)`] THEN
    INTEGER_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[int_divides] THEN DISCH_THEN(X_CHOOSE_TAC `k:int`) THEN
  EXISTS_TAC `k:int` THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `z - N:int = q * k` THEN INT_ARITH_TAC;
    MATCH_MP_TAC KQ_LB THEN EXISTS_TAC `q:int` THEN
    ONCE_REWRITE_TAC[INT_MUL_SYM] THEN ASM_INT_ARITH_TAC;
    MATCH_MP_TAC INT_LE_RMUL_CANCEL THEN EXISTS_TAC `q:int` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((M - N) div q) * q = M - N` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[INT_MUL_DIV_EQ]; ALL_TAC] THEN
    UNDISCH_TAC `z - N:int = q * k` THEN UNDISCH_TAC `z:int <= M` THEN
     INT_ARITH_TAC]);;

let AP_CARD_ARITH = prove
 (`!q M N A:int. &1 <= q /\ q divides (M - N) /\ N <= M /\ M - N <= &2 * A /\
  &0 <= A
                 ==> q * &(num_of_int((M - N) div q - &0 + &1)) <= &2 * A + q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (M - N) div q` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_DIV THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int((M - N) div q - &0 + &1)) = (M - N) div q + &1`
   SUBST1_TAC THENL
   [REWRITE_TAC[INT_SUB_RZERO] THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `q * ((M - N) div q) = M - N` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    ASM_REWRITE_TAC[INT_MUL_DIV_EQ]; ALL_TAC] THEN
  REWRITE_TAC[INT_ADD_LDISTRIB; INT_MUL_RID] THEN ASM_INT_ARITH_TAC);;

let AP_CARD_LE_LMUL = prove
 (`!S q N M A:int r.
      &1 <= q /\ &0 <= A /\ q divides (M - N) /\ N <= M /\
      (!x. x IN S ==> N <= x /\ x <= M /\ q divides (x - r)) /\
       q divides (N - r) /\
      FINITE S
      ==> q * &(CARD S) <= q * &(CARD {k:int | &0 <= k /\
       k <= (M - N) div q})`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\k. N + k * q) {k | &0 <= k /\
   k <= (M - N) div q})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [MATCH_MP_TAC AP_SUBSET_IMAGE THEN EXISTS_TAC `A:int` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:int` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[FINITE_INT_SEG]];
    MATCH_MP_TAC CARD_IMAGE_LE THEN REWRITE_TAC[FINITE_INT_SEG]]);;

let AP_COUNT = prove
 (`!A q r:int. &0 <= A /\ &1 <= q
               ==> q * &(CARD {z:int | abs z <= A /\
                q divides (z - r)}) <= &2 * A + q`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {z:int | abs z <= A /\ q divides (z - r)}` THEN
  SUBGOAL_THEN `FINITE(S:int->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{z:int | --A <= z /\ z <= A}` THEN
    REWRITE_TAC[FINITE_INT_SEG] THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `S:int->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; INT_MUL_RZERO] THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `S:int->bool` INT_FINITE_MAX_ELEMENT) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `S:int->bool` INT_FINITE_MIN_ELEMENT) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `N:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `abs(M:int) <= A /\ q divides (M - r) /\ abs(N:int) <= A /\
   q divides (N - r)`
    STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_binary "IN" (concl th))))
     THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN
     MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(N:int) <= M` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:int) divides (M - N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTEGER_RULE
      `(q:int) divides (M - r) /\ q divides (N - r)
       ==> q divides (M - N)`];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `q * &(CARD {k | &0 <= k /\ k <= (M - N) div q})` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC AP_CARD_LE_LMUL THEN
    MAP_EVERY EXISTS_TAC [`A:int`; `r:int`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:int` THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[];
      SUBGOAL_THEN `x IN {z:int | abs z <= A /\
       q divides (z - r)}` MP_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]]];
    SUBGOAL_THEN `CARD {k | &0 <= k /\ k <= (M - N) div q} <=
                  num_of_int((M - N) div q - &0 + &1)` MP_TAC THENL
     [MATCH_MP_TAC INT_INTERVAL_CARD_LE THEN
      MATCH_MP_TAC INT_LE_DIV THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `q * &(num_of_int((M - N) div q - &0 + &1))` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[INT_LE_LMUL; INT_ARITH `&1 <= (q:int) ==> &0 <= q`;
       INT_OF_NUM_LE];
      MATCH_MP_TAC AP_CARD_ARITH THEN
      REPEAT CONJ_TAC THEN
       (FIRST_ASSUM ACCEPT_TAC ORELSE ASM_INT_ARITH_TAC)]]);;

let SPACING_DIV = INTEGER_RULE
  `!a1 a2 d:int. coprime(a1,a2) /\ a1 divides (a2 * d) ==> a1 divides d`;;

let lincount2 = new_definition
 `lincount2 a1 a2 m A =
    CARD {z2:int | ?z1. a1*z1 + a2*z2 = m /\ abs z1 <= A /\ abs z2 <= A}`;;

let LIN2_EMBED = prove
 (`!a1 a2 m A z2_0 z1_0:int.
      coprime(a1,a2) /\ a1 * z1_0 + a2 * z2_0 = m
      ==> {z2:int | ?z1. a1*z1 + a2*z2 = m /\ abs z1 <= A /\ abs z2 <= A}
          SUBSET {z:int | abs z <= A /\ a1 divides (z - z2_0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `z2:int` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SPACING_DIV THEN EXISTS_TAC `a2:int` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(a2:int) * (z2 - z2_0) = a1 * (z1_0 - z1)` SUBST1_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INTEGER_RULE `(a1:int) divides (a1 * x)`]);;

let LEMMA1_LINCOUNT = prove
 (`!a1 a2 m A:int.
      coprime(a1,a2) /\ ~(a1 = &0) /\ &0 <= A
      ==> abs a1 * &(lincount2 a1 a2 m A) <= &2 * A + abs a1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount2] THEN
  ABBREV_TAC `T2 = {z2:int | ?z1. a1*z1 + a2*z2 = m /\ abs z1 <= A /\
   abs z2 <= A}` THEN
  SUBGOAL_THEN `&1 <= abs(a1:int)` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `T2:int->bool = {}` THENL
   [ASM_REWRITE_TAC[CARD_CLAUSES; INT_MUL_RZERO] THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z2_0:int` MP_TAC) THEN EXPAND_TAC "T2" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1_0:int` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `abs a1 * &(CARD {z:int | abs z <= A /\
   abs a1 divides (z - z2_0)})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
    [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC CARD_SUBSET THEN
     CONJ_TAC THENL
     [REWRITE_TAC[INT_DIVIDES_LABS] THEN
      MP_TAC(ISPECL [`a1:int`;`a2:int`;`m:int`;`A:int`;`z2_0:int`;`z1_0:int`]
        LIN2_EMBED) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
       EXISTS_TAC `{z:int | --A <= z /\ z <= A}` THEN
      REWRITE_TAC[FINITE_INT_SEG; SUBSET; IN_ELIM_THM] THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`A:int`; `abs a1:int`; `z2_0:int`] AP_COUNT) THEN
    ASM_REWRITE_TAC[]]);;

let LEMMA1_LINCOUNT_3A = prove
 (`!a1 a2 m A:int.
      coprime(a1,a2) /\ ~(a1 = &0) /\ &0 <= A /\ abs a1 <= A
      ==> abs a1 * &(lincount2 a1 a2 m A) <= &3 * A`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:int`;`a2:int`;`m:int`;`A:int`] LEMMA1_LINCOUNT) THEN
  ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Set-gcd, Bezout, and the l-variable linear solution count `lincount`      *)
(* ------------------------------------------------------------------------- *)

(* GCD facts (divides both arguments, non-negative, Bezout) are exactly the  *)
(* library specification `int_gcd` (int.ml); used directly below.            *)

let SETGCD_EXISTS = prove
 (`!s:A->bool. FINITE s
     ==> !a:A->int. ?g. (!i. i IN s ==> g divides a i) /\
                        (!d. (!i. i IN s ==> d divides a i) ==> d divides g) /\
                        &0 <= g`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [GEN_TAC THEN EXISTS_TAC `&0:int` THEN
    REWRITE_TAC[NOT_IN_EMPTY; INT_LE_REFL] THEN
    REWRITE_TAC[INTEGER_RULE `(d:int) divides &0`];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `s:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `a:A->int` THEN
  REMOVE_THEN "ih" (MP_TAC o SPEC `a:A->int`) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `gcd((a:A->int) x, g)` THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:A` THEN REWRITE_TAC[IN_INSERT] THEN STRIP_TAC THENL
     [ASM_MESON_TAC[int_gcd];
      MATCH_MP_TAC(INTEGER_RULE
        `!b:int. G divides b /\ b divides c ==> G divides c`) THEN
      EXISTS_TAC `g:int` THEN ASM_SIMP_TAC[int_gcd]];
    X_GEN_TAC `d:int` THEN REWRITE_TAC[IN_INSERT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(d:int) divides (a:A->int) x /\
     d divides g` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `j:A` THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`(a:A->int) x`; `g:int`] int_gcd) THEN
      DISCH_THEN(MP_TAC o last o CONJUNCTS) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:int` (X_CHOOSE_THEN `v:int` SUBST1_TAC)) THEN
      UNDISCH_TAC `(d:int) divides (a:A->int) x` THEN
      UNDISCH_TAC `(d:int) divides g` THEN INTEGER_TAC];
    REWRITE_TAC[int_gcd]]);;

let lincount = new_definition
 `lincount (s:A->bool) (a:A->int) (m:int) (A:int) =
    CARD {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                     (!i. ~(i IN s) ==> z i = &0) /\
                     isum s (\i. a i * z i) = m}`;;

let setcoprime = new_definition
 `setcoprime (s:A->bool) (a:A->int) <=>
    (!d. (!i. i IN s ==> d divides a i) ==> d divides &1)`;;

let SOLSET_FINITE = prove
 (`!s:A->bool a m A. FINITE s
    ==> FINITE {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                           (!i. ~(i IN s) ==> z i = &0) /\
                           isum s (\i. a i * z i) = m}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{z:A->int | (!i. i IN s ==> z i IN {w:int | --A <= w /\
   w <= A}) /\
                          (!i. ~(i IN s) ==> z i = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_FUNSPACE THEN ASM_REWRITE_TAC[FINITE_INT_SEG];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:A->int` THEN
     STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((z:A->int) i) <= A` MP_TAC THENL
     [ASM_SIMP_TAC[]; INT_ARITH_TAC]]);;

let LEMMA2_BASE_CASE = prove
 (`!H K:A a m A:int.
     ~(H = K) /\ ~(a H = &0) /\ &0 <= A /\ abs(a K) <= abs(a H) /\
      abs(a H) <= A /\
     coprime(a H, a K)
     ==> abs(a H) * &(lincount {H,K} a m A) <= &3 * A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `abs(a (H:A)) * &(lincount2 (a H) (a K) m A)` THEN CONJ_TAC THENL
   [ALL_TAC; MATCH_MP_TAC LEMMA1_LINCOUNT_3A THEN ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE; lincount2] THEN
  ABBREV_TAC `SS = {z:A->int | (!i. i IN {H,K} ==> abs(z i) <= A) /\
                (!i. ~(i IN {H,K}) ==> z i = &0) /\
                isum {H,K} (\i. a i * z i) = m}` THEN
  SUBGOAL_THEN
   `!z:A->int. z IN SS ==> a H * z H + a K * z K = m /\
                           (!i. ~(i IN {H,K}) ==> z i = &0)`
   (LABEL_TAC "props") THENL
   [X_GEN_TAC `z:A->int` THEN EXPAND_TAC "SS" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SIMP_TAC[ISUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\z:A->int. z K) SS)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:A->int`; `w:A->int`] THEN STRIP_TAC THEN
      USE_THEN "props" (MP_TAC o SPEC `z:A->int`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "props" (MP_TAC o SPEC `w:A->int`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(CONV_RULE(TRY_CONV(BINOP_CONV BETA_CONV))) THEN
      STRIP_TAC THEN STRIP_TAC THEN
      SUBGOAL_THEN `a (H:A) * (z:A->int) H = a H * (w:A->int) H` MP_TAC THENL
       [MAP_EVERY (fun t -> UNDISCH_TAC t)
          [`a H * (w:A->int) H + a K * w K = m`;
           `a H * (z:A->int) H + a K * z K = m`;
             `(z:A->int) K = (w:A->int) K`] THEN
        CONV_TAC INT_RING; ALL_TAC] THEN
      ASM_SIMP_TAC[INT_EQ_MUL_LCANCEL] THEN DISCH_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:A` THEN
      ASM_CASES_TAC `i:A = H` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `i:A = K` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(z:A->int) i = &0 /\ (w:A->int) i = &0`
        (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[IN_INSERT; NOT_IN_EMPTY];
      MP_TAC(ISPECL [`{H,K}:A->bool`;`a:A->int`;`m:int`;`A:int`] SOLSET_FINITE)
       THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
      MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN EXPAND_TAC "SS" THEN REFL_TAC];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `z2:int` THEN
       DISCH_THEN(X_CHOOSE_THEN `z:A->int` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `(z:A->int) H` THEN
      USE_THEN "props" (MP_TAC o SPEC `z:A->int`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:A->int) IN SS` THEN EXPAND_TAC "SS" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `H:A` th) THEN
       MP_TAC(SPEC `K:A` th)) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{z:int | --A <= z /\ z <= A}` THEN
      REWRITE_TAC[FINITE_INT_SEG; SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[INT_ARITH `abs(z:int) <= A ==> --A <= z /\ z <= A`]]]);;

let PAIR_COPRIME = prove
 (`!x y:int. (!d. d divides x /\
  d divides y ==> d divides &1) ==> coprime(x,y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INTEGER_RULE
   `gcd((x:int),y) divides &1 ==> coprime(x,y)`) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN MESON_TAC[int_gcd]);;

let LEMMA2_CARD2 = prove
 (`!s:A->bool a m A H.
     FINITE s /\ CARD s = 2 /\ setcoprime s a /\ &1 <= A /\ &1 <= abs(a H) /\
     (!i. i IN s ==> abs(a i) <= A) /\ H IN s /\
     (!i. i IN s ==> abs(a i) <= abs(a H))
     ==> abs(a H) * &(lincount s a m A) <= &3 * A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?K:A. ~(H = K) /\ s = {H,K}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(s DELETE (H:A) = {})` MP_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      SUBGOAL_THEN `~(CARD(s DELETE (H:A)) = 0)` MP_TAC THENL
       [ASM_SIMP_TAC[CARD_DELETE] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        ASM_MESON_TAC[CARD_EQ_0; FINITE_DELETE; MEMBER_NOT_EMPTY]];
          ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `K:A` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `~(H:A = K)` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                   NOT_IN_EMPTY] THEN ARITH_TAC]; ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC LEMMA2_BASE_CASE THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_INT_ARITH_TAC;
    ASM_INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `K:A` o check(fun th -> aconv (concl th)
       `!i:A. i IN {H,K} ==> abs((a:A->int) i) <= abs(a H)`)) THEN
    REWRITE_TAC[IN_INSERT] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `H:A` o check(fun th -> aconv (concl th)
       `!i:A. i IN {H,K} ==> abs((a:A->int) i) <= A`)) THEN
    REWRITE_TAC[IN_INSERT] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[];
    MATCH_MP_TAC PAIR_COPRIME THEN X_GEN_TAC `d:int` THEN DISCH_TAC THEN
    UNDISCH_TAC `setcoprime {H,K:A} a` THEN REWRITE_TAC[setcoprime] THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `i:A` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

let FIBER_CARD_BOUND = prove
 (`!(f:X->Y) X c D.
     FINITE X /\ (!y. c * CARD {x | x IN X /\ f x = y} <= D)
     ==> c * CARD X <= CARD (IMAGE f X) * D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:X->Y`; `(\x:X. 1)`; `X:X->bool`] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[GSYM CARD_EQ_NSUM] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum (IMAGE (f:X->Y) X) (\y. D)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    X_GEN_TAC `y:Y` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE {x:X | x IN X /\ (f:X->Y) x = y}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `X:X->bool` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MULT_CLAUSES] THEN ASM_SIMP_TAC[NSUM_CONST] THEN
    ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[NSUM_CONST; FINITE_IMAGE; LE_REFL]]);;

let ISUM_SPLIT_H = prove
 (`!s:A->bool a z:A->int H. FINITE s /\ H IN s
     ==> isum s (\i. a i * z i) = a H * z H + isum (s DELETE H) (\i. a i * z
      i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\i:A. a i * (z:A->int) i`; `s:A->bool`;
    `H:A`] ISUM_DELETE) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let CARD_INTSEG_3A = prove
 (`!A:int. &1 <= A ==> CARD {x:int | --A <= x /\
  x <= A} <= num_of_int(&3 * A)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EXACT_INT_INTERVAL_CARD; INT_ARITH
   `&1 <= A ==> --A:int <= A`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH `&1 <= A ==> &0:int <= &3 * A`;
               INT_ARITH `&1 <= A ==> &0:int <= A - --A + &1`] THEN
  ASM_INT_ARITH_TAC);;

let FUNSPACE_BOUND = prove
 (`!t:A->bool A. FINITE t /\ &1 <= A
    ==> &(CARD {w:A->int | (!i. i IN t ==> abs(w i) <= A) /\
                           (!i. ~(i IN t) ==> w i = &0)})
        <= (&3 * A) pow (CARD t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{w:A->int | (!i. i IN t ==> abs(w i) <= A) /\ (!i. ~(i IN t) ==> w i =
    &0)} =
    {w:A->int | (!i. i IN t ==> w i IN {x:int | --A <= x /\ x <= A}) /\
                (!i. ~(i IN t) ==> w i = &0)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:A->int` THEN
    REWRITE_TAC[INT_ARITH
     `--A <= (x:int) /\ x <= A <=> abs x <= A`]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_FUNSPACE; FINITE_INT_SEG] THEN
  SUBGOAL_THEN `&(num_of_int(&3 * A)):int = &3 * A` (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_LE] THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_SIMP_TAC[CARD_INTSEG_3A]);;

let CASE_A_UNIT = prove
 (`!s:A->bool a H. H IN s /\ setcoprime s a /\
  (!i. i IN s DELETE H ==> a i = &0) /\
                   &1 <= abs(a H)
     ==> abs(a H) = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(a:A->int) H divides &1` MP_TAC THENL
   [UNDISCH_TAC `setcoprime (s:A->bool) a` THEN REWRITE_TAC[setcoprime] THEN
    DISCH_THEN(MP_TAC o SPEC `(a:A->int) H`) THEN ANTS_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN ASM_CASES_TAC `i:A = H` THENL
       [ASM_REWRITE_TAC[INTEGER_RULE `(d:int) divides d`];
        SUBGOAL_THEN `(a:A->int) i = &0`
          (fun th -> REWRITE_TAC[th; INTEGER_RULE `(d:int) divides &0`]) THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]];
      REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP INT_DIVIDES_LE) THEN ASM_INT_ARITH_TAC);;

let CASE_A_INJ = prove
 (`!s:A->bool a m A H.
     FINITE s /\ H IN s /\ abs(a H) = &1 /\ (!i. i IN s DELETE H ==> a i = &0)
     ==> CARD {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                          (!i. ~(i IN s) ==> z i = &0) /\
                          isum s (\i. a i * z i) = m}
         <= CARD {w:A->int | (!i. i IN (s DELETE H) ==> abs(w i) <= A) /\
                             (!i. ~(i IN (s DELETE H)) ==> w i = &0)}`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `X = {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                          (!i. ~(i IN s) ==> z i = &0) /\
                          isum s (\i. a i * z i) = m}` THEN
  SUBGOAL_THEN `!z:A->int. z IN X ==> a H * z H = m` (LABEL_TAC "zH") THENL
   [X_GEN_TAC `z:A->int` THEN EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:A->bool`;`a:A->int`;`z:A->int`;`H:A`] ISUM_SPLIT_H) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `isum (s DELETE H) (\i. a i * (z:A->int) i) = &0`
     SUBST1_TAC THENL
     [MATCH_MP_TAC ISUM_EQ_0 THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:A->int) i = &0` (fun th -> REWRITE_TAC[th;
        INT_MUL_LZERO]) THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INT_ADD_RID] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]); ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\z:A->int i. if i = H then &0 else z i) X)` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:A->int`;`w:A->int`] THEN STRIP_TAC THEN
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:A` THEN
      ASM_CASES_TAC `i:A = H` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `a H * (z:A->int) H = a H * (w:A->int) H` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `~((a:A->int) H = &0)` ASSUME_TAC THENL
         [ASM_INT_ARITH_TAC; ASM_SIMP_TAC[INT_EQ_MUL_LCANCEL]];
        FIRST_X_ASSUM(MP_TAC o check(fun th -> is_eq(concl th) &&
           free_in `H:A` (concl th) && free_in `z:A->int` (concl th))) THEN
        REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `i:A`) THEN
        ASM_REWRITE_TAC[]];
      EXPAND_TAC "X" THEN MATCH_MP_TAC SOLSET_FINITE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `w:A->int` THEN
       DISCH_THEN(X_CHOOSE_THEN `z:A->int` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `i:A` THEN
      REWRITE_TAC[IN_DELETE] THENL
       [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:A->int) IN X` THEN EXPAND_TAC "X" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
        REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `(z:A->int) IN X` THEN EXPAND_TAC "X" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_SIMP_TAC[]];
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{w:A->int | (!i. i IN (s DELETE H) ==> w i IN {x:int | --A <=
       x /\ x <= A}) /\
                              (!i. ~(i IN (s DELETE H)) ==> w i = &0)}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_FUNSPACE THEN
        ASM_SIMP_TAC[FINITE_INT_SEG; FINITE_DELETE];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN GEN_TAC THEN
        MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN MATCH_MP_TAC MONO_FORALL THEN
        GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
        REWRITE_TAC[INT_ARITH
         `--A <= (x:int) /\ x <= A <=> abs x <= A`] THEN
         MESON_TAC[]]]]);;

let LEMMA2_CASE_A = prove
 (`!s:A->bool a m A H.
     FINITE s /\ 3 <= CARD s /\ setcoprime s a /\ &1 <= A /\ &1 <= abs(a H) /\
     H IN s /\ (!i. i IN s DELETE H ==> a i = &0)
     ==> abs(a H) * &(lincount s a m A) <= (&3 * A) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs((a:A->int) H) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC CASE_A_UNIT THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_MUL_LID; lincount] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `&(CARD {w:A->int | (!i. i IN (s DELETE H) ==> abs(w i) <= A) /\
                                 (!i. ~(i IN (s DELETE H)) ==> w i =
                                  &0)}):int` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC CASE_A_INJ THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s DELETE (H:A)`; `A:int`] FUNSPACE_BOUND) THEN
  ASM_SIMP_TAC[FINITE_DELETE] THEN
  SUBGOAL_THEN `CARD(s DELETE (H:A)) = CARD s - 1` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE]; REWRITE_TAC[]]);;

let DELTA_EXISTS = prove
 (`!t:A->bool a. FINITE t /\ (?j. j IN t /\ ~(a j = &0))
    ==> ?delta. &1 <= delta /\ (!i. i IN t ==> delta divides a i) /\
                (!d. (!i. i IN t ==> d divides a i) ==> d divides delta)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `t:A->bool` SETGCD_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:A->int`) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `g:int` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_ARITH
   `&1 <= (g:int) <=> &0 <= g /\ ~(g = &0)`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((a:A->int) j = &0)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `g divides (a:A->int) j` MP_TAC THENL
   [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTEGER_RULE `&0 divides (x:int) <=> x = &0`]]);;

let FIBER_LE_LINCOUNT = prove
 (`!s:A->bool a q delta m A H mp.
     FINITE s /\ H IN s /\ ~(a H = &0) /\
     (!i. i IN (s DELETE H) ==> a i = delta * q i)
     ==> CARD {z:A->int | ((!i. i IN s ==> abs(z i) <= A) /\
                           (!i. ~(i IN s) ==> z i = &0) /\
                           isum s (\i. a i * z i) = m) /\
                          isum (s DELETE H) (\i. q i * z i) = mp}
         <= lincount (s DELETE H) q mp A`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount] THEN
  ABBREV_TAC `t = s DELETE (H:A)` THEN
  ABBREV_TAC `Fset = {z:A->int | ((!i. i IN s ==> abs(z i) <= A) /\
                           (!i. ~(i IN s) ==> z i = &0) /\
                           isum s (\i. a i * z i) = m) /\
                          isum t (\i. q i * z i) = mp}` THEN
  SUBGOAL_THEN `!v:A->int. v IN Fset ==> a H * v H = m - delta * mp` (LABEL_TAC
   "det") THENL
   [X_GEN_TAC `v:A->int` THEN EXPAND_TAC "Fset" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`s:A->bool`;`a:A->int`;`v:A->int`;`H:A`] ISUM_SPLIT_H) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `isum t (\i. a i * (v:A->int) i) = delta * mp`
     SUBST1_TAC THENL
     [SUBGOAL_THEN `isum t (\i. a i * (v:A->int) i) = isum t (\i. delta * (q i
      * v i))`
        SUBST1_TAC THENL
       [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
        REWRITE_TAC[] THEN
        SUBGOAL_THEN `(a:A->int) i = delta * q i` SUBST1_TAC THENL
         [ASM_SIMP_TAC[]; INT_ARITH_TAC]; ALL_TAC] THEN
      REWRITE_TAC[ISUM_LMUL] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\z:A->int i. if i IN t then z i else &0) Fset)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`z:A->int`;`w:A->int`] THEN
      REWRITE_TAC[FUN_EQ_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `!i:A. i IN t ==> (z:A->int) i = w i` (LABEL_TAC "teq")
       THENL
       [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN
         ASM_REWRITE_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `i:A` THEN
      ASM_CASES_TAC `i:A IN t` THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_CASES_TAC `i:A = H` THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `a H * (z:A->int) H = a H * (w:A->int) H` MP_TAC THENL
         [ASM_MESON_TAC[];
          ASM_SIMP_TAC[INT_EQ_MUL_LCANCEL]];
        SUBGOAL_THEN `~(i:A IN s)` ASSUME_TAC THENL
         [EXPAND_TAC "t" THEN ASM_MESON_TAC[IN_DELETE]; ALL_TAC] THEN
        SUBGOAL_THEN `(z:A->int) i = &0` SUBST1_TAC THENL
         [UNDISCH_TAC `(z:A->int) IN Fset` THEN EXPAND_TAC "Fset" THEN
          REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
           FIRST_X_ASSUM MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONV_TAC SYM_CONV THEN
        UNDISCH_TAC `(w:A->int) IN Fset` THEN EXPAND_TAC "Fset" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      EXPAND_TAC "Fset" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                              (!i. ~(i IN s) ==> z i = &0) /\
                              isum s (\i. a i * z i) = m}` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SOLSET_FINITE THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `w:A->int` THEN
       DISCH_THEN(X_CHOOSE_THEN `z:A->int` MP_TAC) THEN
      EXPAND_TAC "Fset" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `i:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `i:A IN s` (fun th -> ASM_SIMP_TAC[th]) THEN
        EXPAND_TAC "t" THEN ASM_MESON_TAC[IN_DELETE];
        X_GEN_TAC `i:A` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `isum t (\i. q i * (if i IN t then (z:A->int) i else &0))
         =
                      isum t (\i. q i * z i)` SUBST1_TAC THENL
         [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]]];
      MP_TAC(ISPECL [`t:A->bool`;`q:A->int`;`mp:int`;`A:int`] SOLSET_FINITE)
       THEN
      ASM_SIMP_TAC[FINITE_DELETE] THEN
      DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "t" THEN
       ASM_SIMP_TAC[FINITE_DELETE]]]);;

let MP_ABS_BOUND = prove
 (`!t:A->bool q z A. FINITE t /\ &0 <= A /\ (!i. i IN t ==> abs(z i) <= A)
    ==> abs(isum t (\i. q i * z i)) <= isum t (\i. abs(q i)) * A`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum t (\i. abs((q:A->int) i * z i))` THEN
  ASM_SIMP_TAC[ISUM_ABS] THEN
  SUBGOAL_THEN `isum t (\i. abs((q:A->int) i)) * A = isum t (\i. abs(q i) * A)`
   SUBST1_TAC THENL
   [REWRITE_TAC[ISUM_RMUL]; ALL_TAC] THEN
  MATCH_MP_TAC ISUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN
   DISCH_TAC THEN
  REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_LMUL THEN
  REWRITE_TAC[INT_ABS_POS] THEN ASM_SIMP_TAC[]);;

let IMAGE_MP_LE = prove
 (`!s:A->bool a q delta m A H.
     FINITE s /\ H IN s /\ &0 <= A /\ &1 <= isum (s DELETE H) (\i. abs(q i)) /\
     (!i. i IN (s DELETE H) ==> a i = delta * q i)
     ==> CARD (IMAGE (\z:A->int. isum (s DELETE H) (\i. q i * z i))
                {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                            (!i. ~(i IN s) ==> z i = &0) /\
                            isum s (\i. a i * z i) = m})
         <= lincount2 (a H) delta m (isum (s DELETE H) (\i. abs(q i)) * A)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount2] THEN
  ABBREV_TAC `t = s DELETE (H:A)` THEN
  ABBREV_TAC `Hs = isum t (\i. abs((q:A->int) i))` THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `mp:int` THEN
     DISCH_THEN(X_CHOOSE_THEN `z:A->int` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(z:A->int) H` THEN
    SUBGOAL_THEN `mp = isum t (\i. (q:A->int) i * z i)` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `abs(isum t (\i. (q:A->int) i * z i)) <= Hs * A`
     ASSUME_TAC THENL
     [EXPAND_TAC "Hs" THEN MATCH_MP_TAC MP_ABS_BOUND THEN
      ASM_SIMP_TAC[FINITE_DELETE] THEN CONJ_TAC THENL
       [EXPAND_TAC "t" THEN ASM_SIMP_TAC[FINITE_DELETE];
        X_GEN_TAC `i:A` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `i:A IN t` THEN EXPAND_TAC "t" THEN
         SIMP_TAC[IN_DELETE]]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`s:A->bool`;`a:A->int`;`z:A->int`;`H:A`] ISUM_SPLIT_H)
      THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `isum t (\i. a i * (z:A->int) i) =
                    delta * isum t (\i. q i * z i)` SUBST1_TAC THENL
       [REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC ISUM_EQ THEN
        X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(a:A->int) i = delta * q i` SUBST1_TAC THENL
         [ASM_SIMP_TAC[]; INT_ARITH_TAC]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `A:int` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
      MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{z:int | --(Hs * A) <= z /\ z <= Hs * A}` THEN
    REWRITE_TAC[FINITE_INT_SEG; SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[INT_ARITH
     `abs(z:int) <= b ==> --b <= z /\ z <= b`]]);;

let FIBER_CARD_BOUND_INT = prove
 (`!(f:X->Y) X (c:int) (D:int).
     FINITE X /\ &0 <= c /\ &0 <= D /\ (!y. c * &(CARD {x | x IN X /\
      f x = y}) <= D)
     ==> c * &(CARD X) <= &(CARD (IMAGE f X)) * D`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:X->Y`; `X:X->bool`; `num_of_int c`;
    `num_of_int D`] FIBER_CARD_BOUND) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&(num_of_int c):int = c /\
   &(num_of_int D):int = D` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ANTS_TAC THENL
   [X_GEN_TAC `y:Y` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
     ASM_REWRITE_TAC[]]);;

let ARGMAX_ABS = prove
 (`!t:A->bool q. FINITE t /\ ~(t = {})
    ==> ?Ht. Ht IN t /\
             (!i. i IN t ==> abs((q:A->int) i) <= abs(q Ht))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (\i:A. abs((q:A->int) i)) t` INT_FINITE_MAX_ELEMENT) THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `M:int` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `Ht:A` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `Ht:A` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN
   DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `abs((q:A->int) i)`) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]]);;

let HS_LE_CARD_HM = prove
 (`!t:A->bool q Ht.
     FINITE t /\ (!i. i IN t ==> abs((q:A->int) i) <= abs(q Ht))
     ==> isum t (\i. abs(q i)) <= &(CARD t) * abs(q Ht)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum t (\i:A. abs((q:A->int) Ht))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_LE THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[ISUM_CONST] THEN REWRITE_TAC[INT_LE_REFL]]);;

let CASE_B_ARITH = prove
 (`!c X Ic Hm Hs A F2 P l:int.
     &1 <= Hm /\ &0 <= c /\ &0 <= A /\ &0 <= F2 /\ &0 <= P /\ &0 <= Ic /\
      &0 <= X /\
     Hm * X <= Ic * (F2 * P) /\ c * Ic <= &3 * (Hs * A) /\ Hs <= l * Hm
     ==> c * X <= (l * F2) * ((&3 * A) * P)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_LCANCEL_IMP THEN EXISTS_TAC `Hm:int` THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `(c:int) * (Ic * (F2 * P))` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(Hm:int) * (c * X) = c * (Hm * X)` SUBST1_TAC THENL
    [INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(c:int) * (Ic * (F2 * P)) = (c * Ic) * (F2 * P)` SUBST1_TAC THENL
   [INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `(&3 * ((Hs:int) * A)) * (F2 * P)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC INT_LE_MUL THEN
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(Hm:int) * (l * F2) * ((&3 * A) * P) =
    (&3 * ((l * Hm) * A)) * (F2 * P)`
    SUBST1_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_ARITH `&3 * ((Hs:int) * A) = (&3 * A) * Hs /\
                           &3 * ((l * Hm) * A) = (&3 * A) * (l * Hm)`] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]];
    MATCH_MP_TAC INT_LE_MUL THEN ASM_REWRITE_TAC[]]);;

let CB_FACT = prove
 (`!s:A->bool. 3 <= CARD s
   ==> (&(CARD s - 1):int) * &(FACT((CARD s - 1) - 1)) =
       &(FACT(CARD s - 1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(s:A->bool) - 1 = SUC((CARD s - 1) - 1)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_MUL] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ASSUME `CARD(s:A->bool) - 1 =
   SUC((CARD s - 1) - 1)`] THEN
  REWRITE_TAC[FACT] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
   FIRST_ASSUM ACCEPT_TAC);;

let CB_POW = prove
 (`!s:A->bool A:int. 3 <= CARD s
   ==> (&3 * A) * (&3 * A) pow ((CARD s - 1) - 1) = (&3 * A) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD(s:A->bool) - 1 = SUC((CARD s - 1) - 1)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [ASSUME `CARD(s:A->bool) - 1 =
   SUC((CARD s - 1) - 1)`] THEN
  REWRITE_TAC[INT_POW]);;

let CASE_B_CORE = prove
 (`!s:A->bool a q delta m A H Ht t.
     FINITE s /\ 3 <= CARD s /\ &1 <= A /\ &1 <= abs(a H) /\ abs(a H) <= A /\
      H IN s /\
     s DELETE H = t /\
     (!i. i IN t ==> a i = delta * q i) /\
     setcoprime t q /\ coprime(a H, delta) /\
     Ht IN t /\ (!i. i IN t ==> abs(q i) <= abs(q Ht)) /\ &1 <= abs(q Ht) /\
     (!i. i IN t ==> abs(q i) <= A) /\
     (!q' m' Ht'. setcoprime t q' /\
      (!i. i IN t ==> abs(q' i) <= abs(q' Ht')) /\
                  (!i. i IN t ==> abs(q' i) <= A) /\ Ht' IN t
                ==> abs(q' Ht') * &(lincount t q' m' A) <=
                    &(FACT(CARD t - 1)) * (&3 * A) pow (CARD t - 1))
     ==> abs(a H) * &(lincount s a m A) <=
         &(FACT(CARD s - 1)) * (&3 * A) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount] THEN
  SUBGOAL_THEN `FINITE (t:A->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_DELETE]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(t:A->bool) = CARD(s:A->bool) - 1` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[CARD_DELETE]; ALL_TAC] THEN
  ABBREV_TAC `Xset = {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                                 (!i. ~(i IN s) ==> z i = &0) /\
                                 isum s (\i. a i * z i) = m}` THEN
  ABBREV_TAC `gproj = \z:A->int. isum t (\i. (q:A->int) i * z i)` THEN
  ABBREV_TAC `Hs = isum (t:A->bool) (\i. abs((q:A->int) i))` THEN
  SUBGOAL_THEN `&1 <= (Hs:int)` (LABEL_TAC "hs1") THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `abs((q:A->int) Ht)` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "Hs" THEN
    SUBGOAL_THEN `&0 <= isum (t DELETE (Ht:A)) (\i. abs((q:A->int) i))`
     MP_TAC THENL
     [MATCH_MP_TAC ISUM_POS_LE THEN REWRITE_TAC[INT_ABS_POS]; ALL_TAC] THEN
    MP_TAC(ISPECL [`\i:A. abs((q:A->int) i)`; `t:A->bool`;
      `Ht:A`] ISUM_DELETE) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((q:A->int) Ht) * &(CARD (Xset:(A->int)->bool)) <=
    &(CARD(IMAGE (gproj:(A->int)->int) Xset)) *
    (&(FACT((CARD(s:A->bool) - 1)-1)) * (&3 * A) pow ((CARD s - 1) - 1))`
   (LABEL_TAC "fiber") THENL
   [MATCH_MP_TAC FIBER_CARD_BOUND_INT THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Xset" THEN MATCH_MP_TAC SOLSET_FINITE THEN ASM_REWRITE_TAC[];
      ASM_INT_ARITH_TAC;
      MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[INT_POS]; MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC];
      X_GEN_TAC `mp:int` THEN
      SUBGOAL_THEN `{x:A->int | x IN Xset /\ (gproj:(A->int)->int) x = mp} =
                    {z:A->int | ((!i. i IN s ==> abs(z i) <= A) /\
                                 (!i. ~(i IN s) ==> z i = &0) /\
                                 isum s (\i. a i * z i) = m) /\
                                isum (s DELETE H) (\i. q i * z i) = mp}`
        SUBST1_TAC THENL
       [MAP_EVERY EXPAND_TAC ["Xset";"gproj"] THEN
        ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `abs((q:A->int) Ht) * &(lincount (s DELETE H) (q:A->int) mp
       A)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
        [INT_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC FIBER_LE_LINCOUNT THEN
        EXISTS_TAC `delta:int` THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(CARD(s:A->bool)-1)-1 = CARD(t:A->bool) - 1`
         SUBST1_TAC THENL
         [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `abs((a:A->int) H) * &(CARD(IMAGE (gproj:(A->int)->int)
    (Xset:(A->int)->bool))) <=
    &3 * (Hs * A)`
   (LABEL_TAC "image") THENL
   [MP_TAC(ISPECL
    [`s:A->bool`;`a:A->int`;`q:A->int`;`delta:int`;`m:int`;`A:int`;`H:A`]
        IMAGE_MP_LE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (\z:A->int. isum (s DELETE H) (\i. (q:A->int) i * z i))
                    {z:A->int | (!i. i IN s ==> abs(z i) <= A) /\
                                (!i. ~(i IN s) ==> z i = &0) /\
                                isum s (\i. a i * z i) = m} =
                  IMAGE (gproj:(A->int)->int) (Xset:(A->int)->bool)`
      SUBST1_TAC THENL
     [MAP_EVERY EXPAND_TAC ["gproj";"Xset"] THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `isum (s DELETE H) (\i. abs((q:A->int) i)) = Hs`
     SUBST1_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `abs((a:A->int) H) * &(lincount2 ((a:A->int) H) delta m (Hs *
     A))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_LMUL THEN
      ASM_REWRITE_TAC[INT_ABS_POS; INT_OF_NUM_LE];
      MP_TAC(ISPECL [`(a:A->int) H`;`delta:int`;`m:int`;`Hs * A:int`]
       LEMMA1_LINCOUNT_3A) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [ASM_INT_ARITH_TAC;
          MATCH_MP_TAC INT_LE_MUL THEN ASM_INT_ARITH_TAC;
          MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `A:int` THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
             GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
            MATCH_MP_TAC INT_LE_RMUL THEN ASM_INT_ARITH_TAC]];
        REWRITE_TAC[INT_MUL_ASSOC]]]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:A->bool` CB_FACT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`s:A->bool`;`A:int`] CB_POW) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CASE_B_ARITH THEN
  MAP_EVERY EXISTS_TAC
   [`&(CARD(IMAGE (gproj:(A->int)->int) (Xset:(A->int)->bool))):int`;
    `abs((q:A->int) Ht)`; `Hs:int`] THEN
  ASM_REWRITE_TAC[INT_ABS_POS; INT_POS] THEN REPEAT CONJ_TAC THENL
   [ASM_INT_ARITH_TAC;
    MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC;
    SUBGOAL_THEN `Hs <= &(CARD(t:A->bool)) * abs((q:A->int) Ht)` MP_TAC THENL
     [EXPAND_TAC "Hs" THEN MATCH_MP_TAC HS_LE_CARD_HM THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let AQ_EXACT = prove
 (`!t:A->bool a delta. &1 <= delta /\ (!i. i IN t ==> delta divides a i)
    ==> (!i. i IN t ==> a i = delta * (a i div delta))`,
  ASM_MESON_TAC[INT_MUL_DIV_EQ; INT_MUL_SYM]);;

let QLE_ABS = prove
 (`!t:A->bool a delta. &1 <= delta /\ (!i. i IN t ==> delta divides a i)
    ==> (!i. i IN t ==> abs(a i div delta) <= abs(a i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `abs((a:A->int) i) = delta * abs(a i div delta)`
   SUBST1_TAC THENL
   [MP_TAC(ISPECL [`t:A->bool`;`a:A->int`;`delta:int`] AQ_EXACT) THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[INT_ABS_MUL] THEN
    ASM_SIMP_TAC[INT_ARITH
     `&1 <= (delta:int) ==> abs delta = delta`]; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
  MATCH_MP_TAC INT_LE_RMUL THEN REWRITE_TAC[INT_ABS_POS] THEN
   ASM_INT_ARITH_TAC);;

let SETCOPRIME_Q = prove
 (`!t:A->bool a delta.
     &1 <= delta /\ (!i. i IN t ==> delta divides a i) /\
     (!d. (!i. i IN t ==> d divides a i) ==> d divides delta)
     ==> setcoprime t (\i. a i div delta)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[setcoprime] THEN X_GEN_TAC `d:int` THEN
   DISCH_TAC THEN
  SUBGOAL_THEN `((delta:int) * d) divides delta` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:A->int) i = delta * (a i div delta)` SUBST1_TAC THENL
     [ASM_MESON_TAC[AQ_EXACT];
      MATCH_MP_TAC(INTEGER_RULE
       `(d:int) divides e ==> (delta * d) divides (delta * e)`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_TAC THEN SUBGOAL_THEN `~((delta:int) = &0)` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `((delta:int) * d) divides delta` THEN
  UNDISCH_TAC `~((delta:int) = &0)` THEN INTEGER_TAC);;

let COPRIME_AH_DELTA = prove
 (`!s:A->bool a delta H.
     setcoprime s a /\ H IN s /\
     (!i. i IN (s DELETE H) ==> delta divides a i)
     ==> coprime(a H, delta)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PAIR_COPRIME THEN
  X_GEN_TAC `d:int` THEN STRIP_TAC THEN
  UNDISCH_TAC `setcoprime (s:A->bool) a` THEN REWRITE_TAC[setcoprime] THEN
  DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
  ASM_CASES_TAC `i:A = H` THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[IN_DELETE; INTEGER_RULE
     `(d:int) divides delta /\ delta divides ai ==> d divides ai`]]);;

let QJ_NZ = prove
 (`!aj delta qj:int. aj = delta * qj /\ ~(aj = &0) ==> &1 <= abs qj`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INT_ARITH `&1 <= abs(x:int) <=> ~(x = &0)`] THEN
  DISCH_TAC THEN UNDISCH_TAC `~((aj:int) = &0)` THEN
   ASM_REWRITE_TAC[INT_MUL_RZERO]);;

let LEMMA2_CASE_B = prove
 (`!s:A->bool a m A H.
     FINITE s /\ 3 <= CARD s /\ setcoprime s a /\ &1 <= A /\ &1 <= abs(a H) /\
     abs(a H) <= A /\ H IN s /\ (!i. i IN s ==> abs(a i) <= A) /\
     (?j. j IN s DELETE H /\ ~(a j = &0)) /\
     (!q' m' Ht'. setcoprime (s DELETE H) q' /\
                  (!i. i IN s DELETE H ==> abs(q' i) <= abs(q' Ht')) /\
                  (!i. i IN s DELETE H ==> abs(q' i) <= A) /\
                   Ht' IN (s DELETE H)
                ==> abs(q' Ht') * &(lincount (s DELETE H) q' m' A) <=
                    &(FACT(CARD(s DELETE H) - 1)) * (&3 * A) pow (CARD(s DELETE
                     H) - 1))
     ==> abs(a H) * &(lincount s a m A) <=
         &(FACT(CARD s - 1)) * (&3 * A) pow (CARD s - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s DELETE (H:A)`;`a:A->int`] DELTA_EXISTS) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[FINITE_DELETE] THEN
   ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `delta:int` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `q = \i:A. (a:A->int) i div delta` THEN
  SUBGOAL_THEN `!i:A. i IN s DELETE H ==> (a:A->int) i = delta * q i`
   (LABEL_TAC "aq") THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC AQ_EXACT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `setcoprime (s DELETE H) (q:A->int)` (LABEL_TAC "sc") THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC SETCOPRIME_Q THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `coprime((a:A->int) H, delta)` (LABEL_TAC "cop") THENL
   [MATCH_MP_TAC COPRIME_AH_DELTA THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i:A. i IN s DELETE H ==> abs((q:A->int) i) <= abs(a i)`
   (LABEL_TAC "qle") THENL
   [EXPAND_TAC "q" THEN MATCH_MP_TAC QLE_ABS THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i:A. i IN s DELETE H ==> abs((q:A->int) i) <= A` (LABEL_TAC
   "qA") THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `abs((a:A->int) i)` THEN CONJ_TAC THENL
     [USE_THEN "qle" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `!i:A. i IN s ==> abs((a:A->int) i) <= A` THEN
      DISCH_THEN MATCH_MP_TAC THEN UNDISCH_TAC `i:A IN s DELETE H` THEN
      SIMP_TAC[IN_DELETE]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s DELETE (H:A)`;`q:A->int`] ARGMAX_ABS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_DELETE] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Ht:A` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&1 <= abs((q:A->int) Ht)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `abs((q:A->int) j)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC QJ_NZ THEN
      MAP_EVERY EXISTS_TAC [`(a:A->int) j`;`delta:int`] THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "aq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  MATCH_MP_TAC CASE_B_CORE THEN
  MAP_EVERY EXISTS_TAC [`q:A->int`;`delta:int`;`Ht:A`;`s DELETE (H:A)`] THEN
  ASM_REWRITE_TAC[]);;

let LEMMA2_WF = prove
 (`!n. !s:A->bool a m A H.
     CARD s = n /\ FINITE s /\ 2 <= CARD s /\ setcoprime s a /\ &0 <= A /\
     (!i. i IN s ==> abs(a i) <= A) /\ H IN s /\
      (!i. i IN s ==> abs(a i) <= abs(a H))
     ==> abs(a H) * &(lincount s a m A) <= &(FACT(CARD s - 1)) * (&3 * A) pow
      (CARD s - 1)`,
  MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`s:A->bool`;`a:A->int`;`m:int`;`A:int`;`H:A`] THEN
   STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `&1 <= abs((a:A->int) H)` ASSUME_TAC THENL
   [REWRITE_TAC[INT_ARITH
     `&1 <= abs(x:int) <=> ~(x = &0)`] THEN DISCH_TAC THEN
    UNDISCH_TAC `setcoprime (s:A->bool) a` THEN REWRITE_TAC[setcoprime] THEN
    DISCH_THEN(MP_TAC o SPEC `&2:int`) THEN ANTS_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(a:A->int) i = &0`
        (fun th -> REWRITE_TAC[th; INTEGER_RULE `(d:int) divides &0`]) THEN
      SUBGOAL_THEN `abs((a:A->int) i) <= abs(a H)` MP_TAC THENL
       [ASM_SIMP_TAC[]; ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      DISCH_TAC THEN MP_TAC(SPECL [`&2:int`;`&1:int`] INT_DIVIDES_LE) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (A:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `abs((a:A->int) H)` THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs((a:A->int) H) <= A` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `CARD(s:A->bool) = 2` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `FACT(2 - 1) = 1` SUBST1_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 - 1 = 1`; FACT] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2 - 1 = 1`; INT_POW_1; INT_MUL_LID] THEN
    MATCH_MP_TAC LEMMA2_CARD2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `3 <= CARD(s:A->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= CARD(s:A->bool)` THEN
    UNDISCH_TAC `~(CARD(s:A->bool) = 2)` THEN
    ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `!i:A. i IN s DELETE H ==> (a:A->int) i = &0` THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `(&3 * (A:int)) pow (CARD(s:A->bool) - 1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC LEMMA2_CASE_A THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
       MATCH_MP_TAC INT_LE_RMUL THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INT_OF_NUM_LE] THEN MESON_TAC[FACT_LT; LE_1];
        MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC]]; ALL_TAC] THEN
  MATCH_MP_TAC LEMMA2_CASE_B THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `~(!i:A. i IN s DELETE H ==> (a:A->int) i = &0)` THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q':A->int`;`m':int`;`Ht':A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD(s:A->bool) - 1`) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `3 <= CARD(s:A->bool)` THEN ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`s DELETE
   (H:A)`;`q':A->int`;`m':int`;`A:int`;`Ht':A`]) THEN
  SUBGOAL_THEN `CARD(s DELETE (H:A)) = CARD(s:A->bool) - 1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    FIRST [CHANGED_TAC(ASM_SIMP_TAC[FINITE_DELETE]);
           UNDISCH_TAC `3 <= CARD(s:A->bool)` THEN ARITH_TAC;
           ASM_REWRITE_TAC[]];
    REWRITE_TAC[]]);;

let LEMMA2_LINCOUNT = prove
 (`!s:A->bool a m A H.
     FINITE s /\ 2 <= CARD s /\ setcoprime s a /\ &0 <= A /\
     (!i. i IN s ==> abs(a i) <= A) /\ H IN s /\
      (!i. i IN s ==> abs(a i) <= abs(a H))
     ==> abs(a H) * &(lincount s a m A) <= &(FACT(CARD s - 1)) * (&3 * A) pow
      (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `CARD(s:A->bool)` LEMMA2_WF) THEN
  DISCH_THEN(MP_TAC o SPECL [`s:A->bool`;`a:A->int`;`m:int`;`A:int`;`H:A`])
   THEN
  ASM_REWRITE_TAC[]);;

let COEFFBOX_FINITE = prove
 (`!s:A->bool A. FINITE s
    ==> FINITE {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
     (!i. ~(i IN s) ==> a i = &0)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{a:A->int | (!i. i IN s ==> a i IN {w:int | --A <= w /\
   w <= A}) /\
                          (!i. ~(i IN s) ==> a i = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_FUNSPACE THEN ASM_REWRITE_TAC[FINITE_INT_SEG];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `a:A->int` THEN
     STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((a:A->int) i) <= A` MP_TAC THENL
     [ASM_SIMP_TAC[]; INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Khinchin Lemma 3 support: homogeneous coefficient scaling                 *)
(* ------------------------------------------------------------------------- *)

let HOMOG_SCALE_EQ = prove
 (`!s (a:A->int) q delta z.
      FINITE s /\ ~(delta = &0) /\ (!i. i IN s ==> a i = delta * q i)
      ==> (isum s (\i. a i * z i) = &0 <=> isum s (\i. q i * z i) = &0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `isum s (\i. (a:A->int) i * z i) = delta * isum s (\i. q i * z
   i)`
    SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC ISUM_EQ THEN
    ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    ASM_SIMP_TAC[] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[INT_ENTIRE]]);;

let LINCOUNT_SCALE = prove
 (`!s (a:A->int) q delta B.
      FINITE s /\ ~(delta = &0) /\
      (!i. i IN s ==> a i = delta * q i) /\ (!i. ~(i IN s) ==> q i = &0)
      ==> lincount s a (&0) B = lincount s q (&0) B`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A->int` THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->int`; `q:A->int`; `delta:int`; `z:A->int`]
    HOMOG_SCALE_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]));;

let DELTA_GE1 = prove
 (`!delta x:int. &0 <= delta /\ delta divides x /\ ~(x = &0) ==> &1 <= delta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((delta:int) = &0)` MP_TAC THENL
   [ASM_MESON_TAC[INTEGER_RULE
     `(delta:int) = &0 /\ delta divides x ==> x = &0`];
    ASM_INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Power-sum bounds and the nonzero-coefficient Lemma 3 family               *)
(* ------------------------------------------------------------------------- *)

let POWER_SUM_LE = prove
 (`!q. !n:num. isum(1..n)(\h. &h pow q) <= &n pow (q+1)`,
  GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ISUM_CLAUSES_NUMSEG; ARITH; INT_POW; INT_MUL_LZERO] THEN
    REWRITE_TAC[INT_POW_ZERO] THEN COND_CASES_TAC THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC n`] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `(&n:int) pow (q+1) + &(SUC n) pow q` THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ADD1; GSYM INT_OF_NUM_ADD] THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1] THEN
  SUBGOAL_THEN
   `((&n:int) + &1) pow q * (&n + &1) =
    (&n + &1) pow q * &n + (&n + &1) pow q`
    SUBST1_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(INT_ARITH
   `(a:int) <= b ==> a + c <= b + c`) THEN
  MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_POW_LE2 THEN INT_ARITH_TAC; INT_ARITH_TAC]);;

let NAT_MUL_SUB1_LE = prove
 (`!d:num. d * (d - 1) <= d * d`,
  REWRITE_TAC[LE_MULT_LCANCEL] THEN ARITH_TAC);;

let DIV_POW_MUL_LE = prove
 (`!A d q:num. (A DIV d) EXP q * d EXP q <= A EXP q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MULT_EXP] THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN
  MP_TAC(SPECL [`A:num`; `d:num`] (CONJUNCT1 DIVISION_SIMP)) THEN ARITH_TAC);;

let EXP_2_LE = prove
 (`!d q:num. 2 <= q ==> d EXP 2 <= d EXP q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[LE_EXP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ARITH] THEN DISJ2_TAC THEN
   ASM_REWRITE_TAC[]);;

let DIV_POW_DDM1_LE = prove
 (`!A d q:num. 2 <= q ==> (A DIV d) EXP q * d * (d - 1) <= A EXP q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(A DIV d) EXP q * d EXP q` THEN REWRITE_TAC[DIV_POW_MUL_LE] THEN
  REWRITE_TAC[GSYM MULT_ASSOC] THEN REWRITE_TAC[LE_MULT_LCANCEL] THEN
   DISJ2_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `d EXP 2` THEN CONJ_TAC THENL
   [REWRITE_TAC[EXP_2; NAT_MUL_SUB1_LE]; ASM_SIMP_TAC[EXP_2_LE]]);;

let SUCN_NM1 = prove
 (`!n:num. 1 <= n ==> SUC n * (n - 1) + 1 = n * n`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[SUC_SUB1; ADD1] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
   ARITH_TAC);;

let DELTA_STEP_ARITH = prove
 (`!n S F1 Aq:num. 1 <= n /\ n * S <= (n - 1) * Aq /\ F1 * SUC n * n <= Aq
      ==> SUC n * (S + F1) <= n * Aq`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `n * (SUC n * (S + F1)) <= n * (n * Aq)` MP_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_CASES_TAC `n = 0` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `SUC n * (n * S) + F1 * SUC n * n` THEN CONJ_TAC THENL
   [REWRITE_TAC[LEFT_ADD_DISTRIB] THEN MATCH_MP_TAC LE_ADD2 THEN
    CONJ_TAC THEN ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `SUC n * ((n - 1) * Aq) + Aq` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[LE_MULT_LCANCEL]; ALL_TAC] THEN
  SUBGOAL_THEN `SUC n * (n - 1) * Aq + Aq = (SUC n * (n - 1) + 1) * Aq`
   SUBST1_TAC THENL
   [REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES; MULT_ASSOC]; ALL_TAC] THEN
  ASM_SIMP_TAC[SUCN_NM1] THEN REWRITE_TAC[MULT_ASSOC; LE_REFL]);;

let DELTA_INV = prove
 (`!A q:num. 2 <= q ==> !n. n * nsum(2..n)(\d. (A DIV d) EXP q) <= (n - 1) * A
  EXP q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH; MULT_CLAUSES] THEN
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `2 <= SUC n <=> 1 <= n`] THEN
  ASM_CASES_TAC `1 <= n` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    SUBGOAL_THEN `n = 0` SUBST_ALL_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH; MULT_CLAUSES] THEN ARITH_TAC] THEN
  REWRITE_TAC[SUC_SUB1] THEN
  MATCH_MP_TAC DELTA_STEP_ARITH THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:num`; `SUC n`; `q:num`] DIV_POW_DDM1_LE) THEN
  ASM_REWRITE_TAC[SUC_SUB1]);;

let CANCEL_A_LE = prove
 (`!A q S:num. 1 <= A /\ A * S <= (A - 1) * A EXP q ==> S <= A EXP q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `A * S <= A * A EXP q` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(A - 1) * A EXP q` THEN
    ASM_REWRITE_TAC[LE_MULT_RCANCEL] THEN DISJ1_TAC THEN ARITH_TAC;
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_CASES_TAC `A = 0` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let DELTA_TAIL = prove
 (`!A q:num. 2 <= q ==> nsum(1..A)(\d. (A DIV d) EXP q) <= 2 * A EXP q`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `A = 0` THENL
   [ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH; LE_0]; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= A` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`\d:num. (A DIV d) EXP q`; `1`;
    `A:num`] NSUM_CLAUSES_LEFT) THEN
  ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
  CONV_TAC(DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[DIV_1] THEN
  SUBGOAL_THEN `nsum(2..A)(\d. (A DIV d) EXP q) <= A EXP q` MP_TAC THENL
   [MATCH_MP_TAC CANCEL_A_LE THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`A:num`; `q:num`] DELTA_INV) THEN ASM_SIMP_TAC[];
    ARITH_TAC]);;

let setgcd = new_definition
 `setgcd (s:A->bool) (a:A->int) =
    @g. (!i. i IN s ==> g divides a i) /\
        (!d. (!i. i IN s ==> d divides a i) ==> d divides g) /\ &0 <= g`;;

let SETGCD = prove
 (`!s:A->bool a. FINITE s
    ==> (!i. i IN s ==> setgcd s a divides a i) /\
        (!d. (!i. i IN s ==> d divides a i) ==> d divides setgcd s a) /\
        &0 <= setgcd s a`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[setgcd] THEN
  CONV_TAC SELECT_CONV THEN ASM_MESON_TAC[SETGCD_EXISTS]);;

let setmaxabs = new_definition
 `setmaxabs (s:A->bool) (a:A->int) =
    abs(a (@H. H IN s /\ (!i. i IN s ==> abs(a i) <= abs(a H))))`;;

let SETMAXABS = prove
 (`!s:A->bool a. FINITE s /\ ~(s = {})
    ==> (!i. i IN s ==> abs(a i) <= setmaxabs s a) /\
        (?H. H IN s /\ setmaxabs s a = abs(a H))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[setmaxabs] THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->int`] ARGMAX_ABS) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(@H. H IN s /\
   (!i. i IN s ==> abs((a:A->int) i) <= abs(a H))) IN s /\
    (!i. i IN s ==> abs((a:A->int) i) <= abs(a (@H. H IN s /\
     (!i. i IN s ==> abs(a i) <= abs(a H)))))`
    MP_TAC THENL
   [CONV_TAC SELECT_CONV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `(@H. H IN s /\
   (!i. i IN s ==> abs((a:A->int) i) <= abs(a H)))` THEN
  ASM_REWRITE_TAC[]);;

let EXACT_BOX_CARD = prove
 (`!s:A->bool t. FINITE s /\ &0 <= t
    ==> CARD {b:A->int | (!i. i IN s ==> abs(b i) <= t) /\
     (!i. ~(i IN s) ==> b i = &0)}
        = (2 * num_of_int t + 1) EXP CARD s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{b:A->int | (!i. i IN s ==> abs(b i) <= t) /\ (!i. ~(i IN s) ==> b i =
    &0)} =
    {b:A->int | (!i. i IN s ==> b i IN {k:int | --t <= k /\ k <= t}) /\
                (!i. ~(i IN s) ==> b i = &0)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    REWRITE_TAC[INT_ABS_BOUNDS] THEN
    MESON_TAC[INT_ARITH `--t <= x <=> x >= --t`;
              INT_ARITH `(--t <= x /\ x <= t) <=> (--t <= x /\ x <= t)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_FUNSPACE; FINITE_INT_SEG] THEN AP_THM_TAC THEN
   AP_TERM_TAC THEN
  MP_TAC(ISPECL [`--t:int`; `t:int`] EXACT_INT_INTERVAL_CARD) THEN
  ANTS_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
    GSYM INT_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&(num_of_int(t - --t + &1)):int = t - --t + &1`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int t):int = t` SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  INT_ARITH_TAC);;

let SETMAX_CHAR = prove
 (`!s:A->bool b h. FINITE s /\ ~(s = {}) /\ 1 <= h /\
  (!i. i IN s ==> abs(b i) <= &h)
    ==> (setmaxabs s b = &h <=> ~(!i. i IN s ==> abs(b i) <= &h - &1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `b:A->int`] SETMAXABS) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `H:A`
   STRIP_ASSUME_TAC)) THEN
  EQ_TAC THEN STRIP_TAC THENL
   [REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `H:A` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `abs((b:A->int) H) = &h` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ASM_INT_ARITH_TAC];
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    DISCH_THEN(X_CHOOSE_THEN `j:A` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `setmaxabs s (b:A->int) <= &h /\ &h <= setmaxabs s (b:A->int)`
      MP_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `abs((b:A->int) j)` THEN
        CONJ_TAC THENL [ASM_INT_ARITH_TAC; ASM_MESON_TAC[]]];
      ASM_INT_ARITH_TAC]]);;

let SHELL_EQ = prove
 (`!s:A->bool h. FINITE s /\ ~(s = {}) /\ 1 <= h
    ==> {b:A->int | (!i. i IN s ==> abs(b i) <= &h) /\
     (!i. ~(i IN s) ==> b i = &0)
                    /\ setmaxabs s b = &h}
        = {b:A->int | (!i. i IN s ==> abs(b i) <= &h) /\
         (!i. ~(i IN s) ==> b i = &0)}
          DIFF {b:A->int | (!i. i IN s ==> abs(b i) <= &h - &1) /\
           (!i. ~(i IN s) ==> b i = &0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `b:A->int` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`s:A->bool`; `b:A->int`; `h:num`] SETMAX_CHAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
    REWRITE_TAC[DE_MORGAN_THM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[DE_MORGAN_THM] THEN
    MP_TAC(ISPECL [`s:A->bool`; `b:A->int`; `h:num`] SETMAX_CHAR) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let BOX_H_CARD = prove
 (`!s:A->bool h. FINITE s
    ==> CARD {b:A->int | (!i. i IN s ==> abs(b i) <= &h) /\
     (!i. ~(i IN s) ==> b i = &0)}
        = (2 * h + 1) EXP CARD s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `&h:int`] EXACT_BOX_CARD) THEN
  REWRITE_TAC[INT_POS; NUM_OF_INT_OF_NUM] THEN ASM_SIMP_TAC[]);;

let BOX_HM1_CARD = prove
 (`!s:A->bool h. FINITE s /\ 1 <= h
    ==> CARD {b:A->int | (!i. i IN s ==> abs(b i) <= &h - &1) /\
     (!i. ~(i IN s) ==> b i = &0)}
        = (2 * h - 1) EXP CARD s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `&h - &1:int`] EXACT_BOX_CARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&1:int <= &h` MP_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_LE]; INT_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `num_of_int(&h - &1) = h - 1` SUBST1_TAC THENL
   [SUBGOAL_THEN `&h - &1 = &(h - 1):int` SUBST1_TAC THENL
     [ASM_SIMP_TAC[INT_OF_NUM_SUB]; ALL_TAC] THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM]; ALL_TAC] THEN
  SUBGOAL_THEN `2 * (h - 1) + 1 = 2 * h - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC]);;

let SHELL_CARD = prove
 (`!s:A->bool h. FINITE s /\ ~(s = {}) /\ 1 <= h
    ==> CARD {b:A->int | (!i. i IN s ==> abs(b i) <= &h) /\
     (!i. ~(i IN s) ==> b i = &0)
                         /\ setmaxabs s b = &h}
        = (2 * h + 1) EXP CARD s - (2 * h - 1) EXP CARD s`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[SHELL_EQ] THEN
  SUBGOAL_THEN
   `{b:A->int | (!i. i IN s ==> abs(b i) <= &h - &1) /\
    (!i. ~(i IN s) ==> b i = &0)}
    SUBSET {b:A->int | (!i. i IN s ==> abs(b i) <= &h) /\
     (!i. ~(i IN s) ==> b i = &0)}`
   ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `b:A->int` THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((b:A->int) i) <= &h - &1` MP_TAC THENL
     [ASM_SIMP_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DIFF; COEFFBOX_FINITE; BOX_H_CARD; BOX_HM1_CARD]);;

let POWER_GAP = prove
 (`!n a:num. (a + 2) EXP (n + 1) <= a EXP (n + 1) + 2 * (n + 1) * (a + 2) EXP
  n`,
  INDUCT_TAC THENL
   [REWRITE_TAC[ADD_CLAUSES; EXP_1; EXP; MULT_CLAUSES] THEN
    ARITH_TAC; ALL_TAC] THEN
  GEN_TAC THEN REWRITE_TAC[ADD1] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `(n + 1) + 1 = SUC(n+1)`] THEN
   REWRITE_TAC[EXP] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(a + 2) * (a EXP (n + 1) + 2 * (n + 1) * (a + 2) EXP n)` THEN
   CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(a + 2) * (a + 2) EXP n = (a + 2) EXP (n + 1)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM ADD1; EXP]; ALL_TAC] THEN
  SUBGOAL_THEN `a EXP (n + 1) <= (a + 2) EXP (n + 1)` ASSUME_TAC THENL
   [MATCH_MP_TAC EXP_MONO_LE_IMP THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN
  SUBGOAL_THEN `(a + 2) * 2 * (n + 1) * (a + 2) EXP n = 2 * (n + 1) * (a + 2)
   EXP (n + 1)`
    SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `(a+2) * 2 * (n+1) * x = 2 * (n+1) * ((a+2) *
    x)`] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `X = (a + 2) EXP (n + 1)` THEN ABBREV_TAC `Y = a EXP (n + 1)` THEN
  SUBGOAL_THEN `(a + 2) * Y = a * Y + 2 * Y` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC(n + 1) = (n + 1) + 1`] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
  ASM_ARITH_TAC);;

let SHELL_COUNT_BOUND = prove
 (`!l h:num. 1 <= l /\ 1 <= h
    ==> (2 * h + 1) EXP l - (2 * h - 1) EXP l <= (2 * l * 3 EXP (l - 1)) * h
     EXP (l - 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `2 * l * (2 * h + 1) EXP (l - 1)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`l - 1`; `2 * h - 1`] POWER_GAP) THEN
    SUBGOAL_THEN `(l - 1) + 1 = l` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(2 * h - 1) + 2 = 2 * h + 1` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ARITH_TAC;
    SUBGOAL_THEN `(2 * l * 3 EXP (l - 1)) * h EXP (l - 1) = 2 * l * (3 * h) EXP
     (l - 1)`
      SUBST1_TAC THENL [REWRITE_TAC[MULT_EXP] THEN ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MULT_ASSOC; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC]);;

let CARD2_NONEMPTY = prove
 (`!s:A->bool. FINITE s /\ 2 <= CARD s ==> ~(s = {})`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `2 <= CARD(s:A->bool)` THEN
  ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC);;

let NONZERO_WITNESS = prove
 (`!s:A->bool b. (!i. ~(i IN s) ==> b i = &0) /\ ~(b = (\i:A. &0))
    ==> ?j. j IN s /\ ~((b:A->int) j = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[FUN_EQ_THM]) THEN
  REWRITE_TAC[NOT_FORALL_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:A` MP_TAC) THEN DISCH_TAC THEN
  EXISTS_TAC `j:A` THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let SETMAXABS_POS = prove
 (`!s:A->bool b. &0 <= setmaxabs s b`,
  REWRITE_TAC[setmaxabs; INT_ABS_POS]);;

let NUMSETMAX_EQ = prove
 (`!s:A->bool b h. num_of_int(setmaxabs s b) = h ==> setmaxabs s b = &h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&(num_of_int(setmaxabs s (b:A->int))):int = setmaxabs s b`
   MP_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    REWRITE_TAC[SETMAXABS_POS]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let SETMAXABS_BOUNDS = prove
 (`!s:A->bool b A'. FINITE s /\ ~(s = {}) /\
  (!i. i IN s ==> abs(b i) <= &A') /\
                    (?j. j IN s /\ ~(b j = &0))
    ==> &1 <= setmaxabs s b /\ setmaxabs s b <= &A'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `b:A->int`] SETMAXABS) THEN
   ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `abs((b:A->int) j)` THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; ASM_SIMP_TAC[]];
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]]);;

let INNER_IMG_SUBSET = prove
 (`!s:A->bool Ap. FINITE s /\ 2 <= CARD s
    ==> !x. (?b:A->int. x = num_of_int(setmaxabs s b) /\
             ((!i. i IN s ==> abs(b i) <= &Ap) /\
              (!i. ~(i IN s) ==> b i = &0) /\ setcoprime s b) /\
             ~(b = (\i:A. &0)))
        ==> 1 <= x /\ x <= Ap`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `b:A->int` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(s:A->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD2_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `?j:A. j IN s /\ ~((b:A->int) j = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC NONZERO_WITNESS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `b:A->int`; `Ap:num`] SETMAXABS_BOUNDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&(num_of_int(setmaxabs s (b:A->int))):int = setmaxabs s b`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    REWRITE_TAC[SETMAXABS_POS]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&1 <= setmaxabs s (b:A->int)` THEN
  UNDISCH_TAC `setmaxabs s (b:A->int) <= &Ap` THEN INT_ARITH_TAC);;

let CNT_DIV_BOUND = prove
 (`!cnt C K h q:num. 1 <= h /\ cnt <= C * h EXP (q + 1)
    ==> cnt * (K DIV h) <= (C * K) * h EXP q`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `(C * h EXP (q + 1)) * (K DIV h)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC LE_MULT2 THEN ASM_REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  REWRITE_TAC[EXP_ADD; EXP_1] THEN
  SUBGOAL_THEN `(C * h EXP q * h) * (K DIV h) = (C * h EXP q) * (h * (K DIV
   h))` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  SUBGOAL_THEN `(C * K) * h EXP q = (C * h EXP q) * K` SUBST1_TAC THENL
   [REWRITE_TAC[MULT_AC]; ALL_TAC] THEN
  REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN REWRITE_TAC[DIV_MUL_LE]);;

let COPRIME_LINCOUNT_DIV = prove
 (`!s:A->bool b B h Ap. FINITE s /\ 2 <= CARD s /\ &0 <= B /\ &Ap <= B /\
  1 <= h /\
     (!i. i IN s ==> abs(b i) <= &Ap) /\ (!i. ~(i IN s) ==> b i = &0) /\
     setcoprime s b /\ (?j. j IN s /\ ~(b j = &0)) /\ setmaxabs s b = &h
    ==> lincount s b (&0) B
        <= (num_of_int(&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1))) DIV
         h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s:A->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[CARD2_NONEMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `b:A->int`] SETMAXABS) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `H:A`
   STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:A->bool`; `b:A->int`; `&0:int`; `B:int`;
    `H:A`] LEMMA2_LINCOUNT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `&Ap:int` THEN ASM_SIMP_TAC[];
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs((b:A->int) i) <= &h /\ &h = abs(b H)`
        (fun th -> MP_TAC(CONJUNCT1 th) THEN MP_TAC(CONJUNCT2 th)) THENL
       [ASM_SIMP_TAC[]; INT_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs((b:A->int) H) = &h` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `K:int = &(FACT(CARD(s:A->bool) - 1)) *
            (&3 * B) pow (CARD s - 1)` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (K:int)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC INT_LE_MUL THEN
    CONJ_TAC THENL [REWRITE_TAC[INT_POS]; MATCH_MP_TAC INT_POW_LE THEN
     ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `h * lincount s (b:A->int) (&0) B <= num_of_int K` MP_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
    SUBGOAL_THEN `&(num_of_int K):int = K` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ; ARITH_RULE `1 <= h ==> ~(h = 0)`]);;

let INNER_FIBER_ENDGAME = prove
 (`!fib C Kn h l:num.
     fib <= C * h EXP (l - 1) /\ 2 <= l /\ 1 <= h
    ==> (&fib:int) * &(Kn DIV h) <= &C * &Kn * &h pow (l - 2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&fib * &(Kn DIV h) = &(fib * (Kn DIV h)):int` SUBST1_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_MUL]; ALL_TAC] THEN
  SUBGOAL_THEN `&C * &Kn * &h pow (l - 2) = &((C * Kn) * h EXP (l - 2)):int`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_POW; GSYM INT_OF_NUM_MUL] THEN
    REWRITE_TAC[INT_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN
  MATCH_MP_TAC CNT_DIV_BOUND THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(l - 2) + 1 = l - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let INNER_FIBER_BOUND = prove
 (`!s:A->bool Ap B h. FINITE s /\ 2 <= CARD s /\ &0 <= B /\ &Ap <= B /\
  1 <= h /\ h <= Ap
    ==> isum {b:A->int | b IN {b:A->int | ((!i. i IN s ==> abs(b i) <= &Ap) /\
                          (!i. ~(i IN s) ==> b i = &0) /\ setcoprime s b) /\
                           ~(b = (\i:A. &0))} /\
                         num_of_int(setmaxabs s b) = h}
             (\b. &(lincount s b (&0) B))
        <= &(2 * CARD s * 3 EXP (CARD s - 1)) *
           (&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1)) * &h pow (CARD s -
            2)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `KI:int = &(FACT(CARD(s:A->bool) - 1)) *
             (&3 * B) pow (CARD s - 1)` THEN
  ABBREV_TAC `Kn = num_of_int(KI:int)` THEN
  ABBREV_TAC `FIB = {b:A->int | b IN {b:A->int | ((!i. i IN s ==> abs(b i) <=
   &Ap) /\
                    (!i. ~(i IN s) ==> b i = &0) /\ setcoprime s b) /\
                     ~(b = (\i:A. &0))} /\
                   num_of_int(setmaxabs s b) = h}` THEN
  SUBGOAL_THEN `&0 <= (KI:int)` ASSUME_TAC THENL
   [EXPAND_TAC "KI" THEN MATCH_MP_TAC INT_LE_MUL THEN
    CONJ_TAC THENL [REWRITE_TAC[INT_POS]; MATCH_MP_TAC INT_POW_LE THEN
     ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&Kn = KI:int` ASSUME_TAC THENL
   [EXPAND_TAC "Kn" THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:A->int. b IN FIB ==>
     (!i. i IN s ==> abs(b i) <= &Ap) /\ (!i. ~(i IN s) ==> b i = &0) /\
      setcoprime s b /\
     (?j. j IN s /\ ~(b j = &0)) /\ setmaxabs s b = &h` (LABEL_TAC "ELT") THENL
   [EXPAND_TAC "FIB" THEN REWRITE_TAC[IN_ELIM_THM] THEN GEN_TAC THEN
    STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(s:A->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[CARD2_NONEMPTY]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NONZERO_WITNESS THEN ASM_MESON_TAC[];
      MATCH_MP_TAC NUMSETMAX_EQ THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (FIB:(A->int)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= &Ap) /\
     (!i. ~(i IN s) ==> a i = &0)}` THEN
    ASM_SIMP_TAC[COEFFBOX_FINITE] THEN EXPAND_TAC "FIB" THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum (FIB:(A->int)->bool) (\b. &(Kn DIV h))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `b:A->int` THEN
    DISCH_TAC THEN
    REWRITE_TAC[INT_OF_NUM_LE] THEN
    REMOVE_THEN "ELT" (MP_TAC o SPEC `b:A->int`) THEN ASM_REWRITE_TAC[] THEN
     STRIP_TAC THEN
    MP_TAC(ISPECL [`s:A->bool`; `b:A->int`; `B:int`; `h:num`;
      `Ap:num`] COPRIME_LINCOUNT_DIV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Kn" THEN EXPAND_TAC "KI" THEN REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ISUM_CONST] THEN
  SUBGOAL_THEN `CARD (FIB:(A->int)->bool) <= (2 * CARD(s:A->bool) * 3 EXP (CARD
   s - 1)) * h EXP (CARD s - 1)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD {b:A->int | (!i. i IN s ==> abs(b i) <= &h) /\
     (!i. ~(i IN s) ==> b i = &0)
                       /\ setmaxabs s b = &h}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `b:A->int` THEN
        DISCH_TAC THEN
        REMOVE_THEN "ELT" (MP_TAC o SPEC `b:A->int`) THEN
         ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
        SUBGOAL_THEN `abs((b:A->int) i) <= setmaxabs s b` MP_TAC THENL
         [MP_TAC(ISPECL [`s:A->bool`; `b:A->int`] SETMAXABS) THEN
          ANTS_TAC THENL [ASM_MESON_TAC[CARD2_NONEMPTY]; ASM_MESON_TAC[]];
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= &h) /\
         (!i. ~(i IN s) ==> a i = &0)}` THEN
        ASM_SIMP_TAC[COEFFBOX_FINITE] THEN
         REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
      SUBGOAL_THEN `~(s:A->bool = {})` ASSUME_TAC THENL
       [ASM_MESON_TAC[CARD2_NONEMPTY]; ALL_TAC] THEN
      ASM_SIMP_TAC[SHELL_CARD] THEN MATCH_MP_TAC SHELL_COUNT_BOUND THEN
       ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&(2 * CARD(s:A->bool) * 3 EXP (CARD s - 1)) * (KI:int) *
    &h pow (CARD s - 2) =
                &(2 * CARD s * 3 EXP (CARD s - 1)) * &Kn * &h pow (CARD s - 2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INNER_FIBER_ENDGAME THEN ASM_REWRITE_TAC[]);;

let INNER_COPRIME_BOUND = prove
 (`!s:A->bool Ap B. FINITE s /\ 2 <= CARD s /\ &0 <= B /\ &Ap <= B
    ==> isum {b:A->int | ((!i. i IN s ==> abs(b i) <= &Ap) /\
     (!i. ~(i IN s) ==> b i = &0) /\
                          setcoprime s b) /\ ~(b = (\i:A. &0))}
             (\b. &(lincount s b (&0) B))
        <= (&(2 * CARD s * 3 EXP (CARD s - 1)) *
            (&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1))) * &Ap pow (CARD
             s - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`\b:A->int. num_of_int(setmaxabs s b)`;
     `\b:A->int. (&(lincount s b (&0) B):int)`;
     `{b:A->int | ((!i. i IN s ==> abs(b i) <= &Ap) /\ (!i. ~(i IN s) ==> b i =
      &0) /\
                   setcoprime s b) /\ ~(b = (\i:A. &0))}`;
     `1..Ap`] ISUM_GROUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= &Ap) /\
       (!i. ~(i IN s) ==> a i = &0)}` THEN
      ASM_SIMP_TAC[COEFFBOX_FINITE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
       MESON_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; IN_NUMSEG] THEN
       X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`s:A->bool`; `Ap:num`] INNER_IMG_SUBSET) THEN
       ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN MATCH_MP_TAC MONO_IMP THEN
      REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum(1..Ap)(\h. (&(2 * CARD(s:A->bool) * 3 EXP (CARD s - 1)) *
              (&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1))) * &h pow (CARD
               s - 2))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_LE_NUMSEG THEN X_GEN_TAC `h:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MP_TAC(ISPECL [`s:A->bool`; `Ap:num`; `B:int`;
      `h:num`] INNER_FIBER_BOUND) THEN
    ASM_REWRITE_TAC[INT_MUL_ASSOC];
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_LMUL] THEN
  MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_POS];
      MATCH_MP_TAC INT_LE_MUL THEN
      CONJ_TAC THENL [REWRITE_TAC[INT_POS]; MATCH_MP_TAC INT_POW_LE THEN
       ASM_INT_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`CARD(s:A->bool) - 2`; `Ap:num`] POWER_SUM_LE) THEN
  SUBGOAL_THEN `(CARD(s:A->bool) - 2) + 1 = CARD s - 1` SUBST1_TAC THENL
   [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let REDTUP_NZ = prove
 (`!aj d:int. &1 <= d /\ ~(aj = &0) /\
  aj = d * (aj div d) ==> ~(aj div d = &0)`,
  REPEAT STRIP_TAC THEN UNDISCH_TAC `~(aj:int = &0)` THEN REWRITE_TAC[] THEN
  ONCE_ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[INT_MUL_RZERO]);;

let REDTUP_BIBOUND = prove
 (`!ai d:int. !A:num. &1 <= d /\ abs(ai) <= &A /\ ai = d * (ai div d)
    ==> abs(ai div d) <= &(A DIV (num_of_int d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(d:int) * abs(ai div d) <= &A` ASSUME_TAC THENL
   [SUBGOAL_THEN `d * abs(ai div d) = abs(ai:int)` SUBST1_TAC THENL
     [GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
       [ASSUME `(ai:int) = d * (ai div d)`]
      THEN
      REWRITE_TAC[INT_ABS_MUL] THEN
       ASM_SIMP_TAC[INT_ARITH `&1 <= (d:int) ==> abs d = d`];
      ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `~(num_of_int d = 0)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LT_NZ; GSYM INT_OF_NUM_LT] THEN
    SUBGOAL_THEN `&(num_of_int d):int = d` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
      ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(ai div d) = &(num_of_int(abs(ai div d)))` ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    REWRITE_TAC[INT_ABS_POS];
    ALL_TAC] THEN
  ONCE_ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_OF_NUM_LE] THEN
  ASM_SIMP_TAC[LE_RDIV_EQ] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&(num_of_int d):int = d` SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM(ASSUME `abs(ai div d) = &(num_of_int(abs(ai div
   d)))`)]);;

let REDTUP_PROPS = prove
 (`!s:A->bool a A B. FINITE s /\ 2 <= CARD s /\
  (!i. i IN s ==> abs(a i) <= &A) /\
     (!i. ~(i IN s) ==> a i = &0) /\ (?j. j IN s /\ ~(a j = &0))
    ==> &1 <= setgcd s a /\
        (!i. i IN s ==> a i = setgcd s a * (a i div setgcd s a)) /\
        setcoprime s (\i. if i IN s then a i div setgcd s a else &0) /\
        (!i. i IN s ==> abs((if i IN s then a i div setgcd s a else &0))
                        <= &(A DIV (num_of_int(setgcd s a)))) /\
        (!i. ~(i IN s) ==> (if i IN s then a i div setgcd s a else &0) = &0) /\
        ~((\i. if i IN s then a i div setgcd s a else &0) = (\i:A. &0)) /\
        lincount s a (&0) B = lincount s (\i. if i IN s then a i div setgcd s a
         else &0) (&0) B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->int`] SETGCD) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
  ABBREV_TAC `d = setgcd s (a:A->int)` THEN
  SUBGOAL_THEN `&1 <= (d:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC DELTA_GE1 THEN EXISTS_TAC `(a:A->int) j` THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = \i:A. if i IN s then (a:A->int) i div d else &0` THEN
  SUBGOAL_THEN
   `!i:A. i IN s ==> (a:A->int) i = (d:int) * (q:A->int) i`
   (LABEL_TAC "aq") THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN EXPAND_TAC "q" THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN ONCE_REWRITE_TAC[INT_MUL_SYM] THEN
    REWRITE_TAC[INT_MUL_DIV_EQ] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i:A. ~(i IN s) ==> (q:A->int) i = &0`
   (LABEL_TAC "qz") THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN EXPAND_TAC "q" THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:A. i IN s ==> (a:A->int) i = (d:int) * (a i div d)`
   (LABEL_TAC "aqd") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(a:A->int) i = d * q i` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "q" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REWRITE_TAC[setcoprime] THEN X_GEN_TAC `e:int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `((d:int) * e) divides d` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check(is_forall o concl)) THEN
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(a:A->int) i = d * q i` SUBST1_TAC THENL
       [ASM_SIMP_TAC[];
        MATCH_MP_TAC(INTEGER_RULE
         `(e:int) divides q ==> (d * e) divides (d * q)`)
         THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN EXPAND_TAC "q" THEN
         ASM_REWRITE_TAC[]];
      MATCH_MP_TAC(INTEGER_RULE
       `~((d:int) = &0) ==> (d * e) divides d ==> e divides &1`) THEN
      ASM_INT_ARITH_TAC];
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN EXPAND_TAC "q" THEN
     ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REDTUP_BIBOUND THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]; USE_THEN "aqd" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[];
    REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `j:A`) THEN
    EXPAND_TAC "q" THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((a:A->int) j div d = &0)` MP_TAC THENL
     [MATCH_MP_TAC REDTUP_NZ THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; USE_THEN "aqd" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]];
      MESON_TAC[]];
    MATCH_MP_TAC LINCOUNT_SCALE THEN EXISTS_TAC `d:int` THEN
    ASM_SIMP_TAC[INT_ARITH `&1 <= (d:int) ==> ~(d = &0)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]]]);;

let FIBER_RESCALE = prove
 (`!s:A->bool A B dn. FINITE s /\ 2 <= CARD s /\ 1 <= dn
    ==> isum {a:A->int | (a IN ({a:A->int | (!i. i IN s ==> abs(a i) <= &A) /\
                          (!i. ~(i IN s) ==> a i = &0)} DIFF {(\i:A. &0)})) /\
                         num_of_int(setgcd s a) = dn}
             (\a. &(lincount s a (&0) B))
        <= isum {b:A->int | ((!i. i IN s ==> abs(b i) <= &(A DIV dn)) /\
                             (!i. ~(i IN s) ==> b i = &0) /\ setcoprime s b) /\
                              ~(b = (\i:A. &0))}
                (\b. &(lincount s b (&0) B))`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ISUM_LE_INCLUDED THEN
  EXISTS_TAC `\b:A->int. (\k:A. if k IN s then &dn * b k else &0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= &A) /\
     (!i. ~(i IN s) ==> a i = &0)}` THEN
    ASM_SIMP_TAC[COEFFBOX_FINITE] THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= &(A DIV dn)) /\
     (!i. ~(i IN s) ==> a i = &0)}` THEN
    ASM_SIMP_TAC[COEFFBOX_FINITE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[INT_POS]; ALL_TAC] THEN
  X_GEN_TAC `a:A->int` THEN REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_SING] THEN
   STRIP_TAC THEN
  EXISTS_TAC `\k:A. if k IN s then (a:A->int) k div setgcd s a else &0` THEN
  SUBGOAL_THEN `?j:A. j IN s /\ ~((a:A->int) j = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC NONZERO_WITNESS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->int`; `A:num`; `B:int`] REDTUP_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->int`] SETGCD) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `setgcd s (a:A->int) = &dn` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `num_of_int(setgcd s (a:A->int)) =
    dn`
                            then SUBST1_TAC(SYM th) else NO_TAC) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
     ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i:A. i IN s ==> abs((if i IN s then (a:A->int) i div setgcd s a else &0))
    <= &(A DIV dn)`
   ASSUME_TAC THENL
   [X_GEN_TAC `i:A` THEN DISCH_TAC THEN EXPAND_TAC "dn" THEN
    UNDISCH_TAC `!i. i IN s ==> abs((if i IN s then (a:A->int) i div setgcd s a
     else &0)) <= &(A DIV (num_of_int(setgcd s a)))` THEN
    DISCH_THEN(MP_TAC o SPEC `i:A`) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `k:A` THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_MUL_DIV_EQ] THEN
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[INT_LE_REFL]]);;

let GCD_IMG_SUBSET = prove
 (`!s:A->bool A. FINITE s /\ 2 <= CARD s /\ &1 <= A
    ==> !x. (?a:A->int. x = num_of_int(setgcd s a) /\
             (a IN ({a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
              (!i. ~(i IN s) ==> a i = &0)}
                    DIFF {(\i:A. &0)})))
        ==> 1 <= x /\ x <= num_of_int A`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A->int` MP_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_SING] THEN
  DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?j:A. j IN s /\ ~((a:A->int) j = &0)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC NONZERO_WITNESS THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:A->bool`; `a:A->int`] SETGCD) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= setgcd s (a:A->int)` ASSUME_TAC THENL
   [MATCH_MP_TAC DELTA_GE1 THEN EXISTS_TAC `(a:A->int) j` THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `setgcd s (a:A->int) <= A` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `abs((a:A->int) j)` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`setgcd s (a:A->int)`;
       `(a:A->int) j`] INT_DIVIDES_LE) THEN
      ASM_SIMP_TAC[] THEN ASM_INT_ARITH_TAC;
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int(setgcd s (a:A->int))):int = setgcd s a`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int A):int = A` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN
  ASM_INT_ARITH_TAC);;

let PERDN_BOUND = prove
 (`!s:A->bool Anat B dn. FINITE s /\ 2 <= CARD s /\ &Anat <= B /\ 1 <= dn
    ==> isum {a:A->int | (a IN ({a:A->int | (!i. i IN s ==> abs(a i) <= &Anat)
     /\
                          (!i. ~(i IN s) ==> a i = &0)} DIFF {(\i:A. &0)})) /\
                         num_of_int(setgcd s a) = dn}
             (\a. &(lincount s a (&0) B))
        <= (&(2 * CARD s * 3 EXP (CARD s - 1)) *
            (&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1))) * &(Anat DIV dn)
             pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum {b:A->int | ((!i. i IN s ==> abs(b i) <= &(Anat DIV dn)) /\
                             (!i. ~(i IN s) ==> b i = &0) /\ setcoprime s b) /\
                              ~(b = (\i:A. &0))}
                (\b. &(lincount s b (&0) B))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC FIBER_RESCALE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INNER_COPRIME_BOUND THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC;
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `&Anat:int` THEN ASM_REWRITE_TAC[INT_OF_NUM_LE; DIV_LE]]]);;

let DELTA_TAIL_INT = prove
 (`!An q:num. 2 <= q ==> isum(1..An)(\dn. &(An DIV dn) pow q) <= &2 * &An pow
  q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `isum(1..An)(\dn. &(An DIV dn) pow q) = &(nsum(1..An)(\dn. (An
   DIV dn) EXP q))`
    SUBST1_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_ISUM_NUMSEG] THEN MATCH_MP_TAC ISUM_EQ THEN
    REWRITE_TAC[IN_NUMSEG; INT_OF_NUM_POW]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 * &An pow q = &(2 * An EXP q):int` SUBST1_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL]; ALL_TAC] THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_SIMP_TAC[DELTA_TAIL]);;

let NONZERO_FAMILY = prove
 (`!s:A->bool. FINITE s /\ 2 < CARD s
    ==> ?Cnz. !A B:int. &1 <= A /\ A <= B
            ==> isum ({a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
                                  (!i. ~(i IN s) ==> a i = &0)} DIFF {(\i:A.
                                   &0)})
                     (\a. &(lincount s a (&0) B))
                <= Cnz * (A * B) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `(&4:int) * &(CARD(s:A->bool)) * &3 pow (2 * (CARD s - 1)) *
    &(FACT(CARD s - 1))` THEN
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `An = num_of_int A` THEN
  SUBGOAL_THEN `(A:int) = &An` ASSUME_TAC THENL
   [EXPAND_TAC "An" THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD(s:A->bool)` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD(s:A->bool) - 1` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1:int) <= &An` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{a:A->int | (!i. i IN s ==> abs(a i) <= A) /\ (!i. ~(i IN s) ==> a i =
    &0)} DIFF {(\i:A. &0)}
    = {a:A->int | (!i. i IN s ==> abs(a i) <= &An) /\
     (!i. ~(i IN s) ==> a i = &0)} DIFF {(\i:A. &0)}`
   SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\a:A->int. num_of_int(setgcd s a)`;
    `\a:A->int. (&(lincount s a (&0) B):int)`;
    `{a:A->int | (!i. i IN s ==> abs(a i) <= &An) /\ (!i. ~(i IN s) ==> a i =
     &0)} DIFF {(\i:A. &0)}`;
    `1..An`] ISUM_GROUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_DIFF THEN MATCH_MP_TAC COEFFBOX_FINITE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_NUMSEG] THEN X_GEN_TAC `k:num` THEN
      MP_TAC(ISPECL [`s:A->bool`; `&An:int`] GCD_IMG_SUBSET) THEN
      ASM_REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
      DISCH_THEN(MP_TAC o SPEC `k:num`) THEN MATCH_MP_TAC MONO_IMP THEN
      REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum(1..An)(\dn. (&(2 * CARD(s:A->bool) * 3 EXP (CARD s - 1)) *
              (&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1))) * &(An DIV dn)
               pow (CARD s - 1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_LE_NUMSEG THEN X_GEN_TAC `dn:num` THEN STRIP_TAC THEN
    CONV_TAC(DEPTH_CONV BETA_CONV) THEN
    MATCH_MP_TAC PERDN_BOUND THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ISUM_LMUL] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `((&(2 * CARD(s:A->bool) * 3 EXP (CARD s - 1)):int) *
               (&(FACT(CARD s - 1)) * (&3 * B) pow (CARD s - 1))) *
              (&2 * &An pow (CARD s - 1))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_POS] THEN
      MATCH_MP_TAC INT_LE_MUL THEN REWRITE_TAC[INT_POS] THEN
      MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC;
      MATCH_MP_TAC DELTA_TAIL_INT THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INT_POW_MUL; GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW] THEN
  REWRITE_TAC[MULT_2; INT_POW_ADD] THEN
  MATCH_MP_TAC(INT_ARITH `(x:int) = y ==> x <= y`) THEN
  CONV_TAC INT_RING);;

let BOX_CARD_LE = prove
 (`!s:A->bool A. FINITE s /\ &0 <= A
    ==> CARD {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
                         (!i. ~(i IN s) ==> a i = &0)}
        <= (2 * num_of_int A + 1) EXP CARD s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `A:int`] EXACT_BOX_CARD) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; LE_REFL]));;

let ZEROFN_LINCOUNT_LE = prove
 (`!s:A->bool B. FINITE s /\ &0 <= B
    ==> lincount s (\i. &0) (&0) B <= (2 * num_of_int B + 1) EXP CARD s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount] THEN
  SUBGOAL_THEN
   `{z:A->int | (!i. i IN s ==> abs(z i) <= B) /\
                (!i. ~(i IN s) ==> z i = &0) /\
                isum s (\i. &0 * z i) = &0} =
    {a:A->int | (!i. i IN s ==> abs(a i) <= B) /\
                (!i. ~(i IN s) ==> a i = &0)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `z:A->int` THEN
    REWRITE_TAC[INT_MUL_LZERO; ISUM_0] THEN MESON_TAC[];
    ASM_SIMP_TAC[BOX_CARD_LE]]);;

let CARDPOW_CAST = prove
 (`!B:int n. &0 <= B ==> &((2 * num_of_int B + 1) EXP n) = (&2 * B + &1) pow
  n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN AP_THM_TAC THEN
   AP_TERM_TAC THEN
  REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
  SUBGOAL_THEN `&(num_of_int B):int = B` SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; INT_ARITH_TAC]);;

let ZEROTERM_BOUND = prove
 (`!s:A->bool A B C0. 1 <= CARD s /\ (&1:int) <= A /\ A <= B /\
                      B <= C0 * A pow (CARD s - 1) /\ &1 <= C0
    ==> (&3 * B) pow (CARD s) <= (&3 pow (CARD s) * C0) * (A * B) pow (CARD s -
     1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(&3:int) pow (CARD(s:A->bool)) =
                &3 * &3 pow (CARD s - 1)`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `CARD(s:A->bool) = SUC(CARD s - 1)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [UNDISCH_TAC `1 <= CARD(s:A->bool)` THEN ARITH_TAC; REWRITE_TAC[INT_POW]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&3 * (B:int)) pow (CARD(s:A->bool)) =
    (&3 * &3 pow (CARD s - 1)) * B * B pow (CARD s - 1)`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `CARD(s:A->bool) = SUC(CARD s - 1)`
      (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [UNDISCH_TAC `1 <= CARD(s:A->bool)` THEN ARITH_TAC;
      REWRITE_TAC[INT_POW; INT_POW_MUL] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INT_POW_MUL] THEN
  ABBREV_TAC `l1 = CARD(s:A->bool) - 1` THEN
  SUBGOAL_THEN
   `(&3 * &3 pow l1) * (B:int) * B pow l1 =
    ((&3 * &3 pow l1) * B pow l1) * B /\
    ((&3 * &3 pow l1) * C0) * A pow l1 * B pow l1 =
    ((&3 * &3 pow l1) * B pow l1) * (C0 * A pow l1)`
   (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
       [INT_ARITH_TAC;
        MATCH_MP_TAC INT_POW_LE THEN INT_ARITH_TAC];
      MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

let ZEROTERM_FINAL = prove
 (`!s:A->bool A B C0. FINITE s /\ 1 <= CARD s /\ &1 <= A /\ A <= B /\
                      B <= C0 * A pow (CARD s - 1) /\ &1 <= C0
    ==> &(lincount s (\i. &0) (&0) B) <= (&3 pow (CARD s) * C0) * (A * B) pow
     (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (B:int)` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `(&3 * (B:int)) pow (CARD(s:A->bool))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `&((2 * num_of_int B + 1) EXP CARD(s:A->bool)):int` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC ZEROFN_LINCOUNT_LE THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[CARDPOW_CAST] THEN
      MATCH_MP_TAC INT_POW_LE2 THEN ASM_INT_ARITH_TAC];
    MATCH_MP_TAC ZEROTERM_BOUND THEN ASM_REWRITE_TAC[]]);;

let FAMILY_SPLIT = prove
 (`!s:A->bool A B. FINITE s /\ &1 <= A
    ==> isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
     (!i. ~(i IN s) ==> a i = &0)}
             (\a. &(lincount s a (&0) B))
        = &(lincount s (\i. &0) (&0) B) +
          isum ({a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
           (!i. ~(i IN s) ==> a i = &0)}
                DIFF {(\i:A. &0)}) (\a. &(lincount s a (&0) B))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{(\i:A. &0)} SUBSET
     {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
      (!i. ~(i IN s) ==> a i = &0)}`
   ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_SING] THEN X_GEN_TAC `a:A->int` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_ABS_NUM] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\a:A->int. (&(lincount s a (&0) B):int)`;
      `{a:A->int | (!i. i IN s ==> abs(a i) <= A) /\ (!i. ~(i IN s) ==> a i =
       &0)}`;
      `{(\i:A. &0:int)}`] ISUM_DIFF) THEN
  ASM_SIMP_TAC[COEFFBOX_FINITE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[ISUM_SING] THEN CONV_TAC(DEPTH_CONV BETA_CONV) THEN
  ABBREV_TAC `X = isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
   (!i. ~(i IN s) ==> a i = &0)}
             (\a. &(lincount s a (&0) B))` THEN
  ABBREV_TAC `cz:int = &(lincount s (\i:A. &0) (&0) B)` THEN
  INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Khinchin Sec.4 / the difference polynomial `ipoly` and its algebra        *)
(* ------------------------------------------------------------------------- *)

let AMGM2 = prove
 (`!a b:num. 2 * a * b <= a * a + b * b`,
  REPEAT GEN_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `a <= b \/ b <= a:num`) THEN
  POP_ASSUM(X_CHOOSE_THEN `d:num` SUBST1_TAC o REWRITE_RULE[LE_EXISTS]) THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB; RIGHT_ADD_DISTRIB; MULT_CLAUSES] THEN
   ARITH_TAC);;

let LEMMA4 = prove
 (`!(A:int->num) (B:int->num) c s.
        FINITE s /\
        (!x. ~(x IN s) ==> A x = 0) /\ (!x. ~(x IN s) ==> B x = 0) /\
        (!x. x IN s ==> c - x IN s)
        ==> 2 * nsum s (\x. A x * B(c - x))
            <= nsum s (\x. A x * A x) + nsum s (\x. B x * B x)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum s (\x. (A:int->num) x * A x + B(c - x) * B(c - x))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `2 * nsum s (\x. (A:int->num) x * B(c - x)) =
      nsum s (\x. 2 * (A x * B(c - x)))`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM NSUM_LMUL]; ALL_TAC] THEN
    MATCH_MP_TAC NSUM_LE THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:int` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN
    MP_TAC(SPECL [`(A:int->num) x`; `(B:int->num)(c - x)`] AMGM2) THEN
    REWRITE_TAC[MULT_ASSOC] THEN ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_ADD] THEN
  MATCH_MP_TAC(ARITH_RULE `b:num = b' ==> a + b <= a + b'`) THEN
  MP_TAC(ISPECL [`\x:int. c - x`; `\y:int. (B:int->num) y * B y`;
    `s:int->bool`]
    NSUM_IMAGE) THEN
  ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:int. c - x) s = s` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN X_GEN_TAC `y:int` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_SIMP_TAC[]; DISCH_TAC THEN EXISTS_TAC `c - y:int` THEN
      ASM_SIMP_TAC[] THEN INT_ARITH_TAC];
    REWRITE_TAC[o_DEF] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let ipoly = new_definition
 `ipoly (f:num->int) e (x:int) = isum(0..e)(\i. f i * x pow i)`;;

let IPOLY_SHIFT_SUM = prove
 (`!k c y:int. y * isum(0..k)(\j. c j * y pow j) = isum(0..k)(\j. c j * y pow
  (j+1))`,
  REPEAT GEN_TAC THEN GEN_REWRITE_TAC (LAND_CONV) [INT_MUL_SYM] THEN
  REWRITE_TAC[GSYM ISUM_RMUL] THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_POW_ADD; INT_POW_1] THEN CONV_TAC INT_RING);;

let POLY_REINDEX = prove
 (`!e (g:num->int) y.
      isum (0..SUC e) (\j. (if j = 0 then &0 else g (j - 1)) * y pow j) =
      isum(0..e)(\j. g j * y pow (j+1))`,
  INDUCT_TAC THEN REPEAT GEN_TAC THENL
   [SIMP_TAC[ISUM_CLAUSES_NUMSEG; LE_0; ARITH] THEN CONV_TAC INT_RING;
    FIRST_X_ASSUM(MP_TAC o SPECL [`g:num->int`; `y:int`]) THEN
    REWRITE_TAC[ISUM_CLAUSES_NUMSEG; LE_0; NOT_SUC; SUC_SUB1] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ADD1] THEN CONV_TAC INT_RING]);;

let IPOLY_SUC = prove
 (`!f e x:int. ipoly f (SUC e) x = ipoly f e x + f(SUC e) * x pow (SUC e)`,
  REWRITE_TAC[ipoly; ISUM_CLAUSES_NUMSEG; LE_0]);;

let ibox = new_definition
 `ibox t M =
  {z:num->int | (!i. i IN 1..t ==> abs(z i) <= M) /\
   (!i. ~(i IN 1..t) ==> z i = &0)}`;;

let IBOX_FINITE = prove
 (`!t M. FINITE(ibox t M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox] THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{z:num->int | (!i. i IN 1..t ==> z i IN {w:int | --M <= w /\
   w <= M}) /\ (!i. ~(i IN 1..t) ==> z i = &0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_FUNSPACE THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_INT_SEG];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `z:num->int` THEN
     STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `abs((z:num->int) i) <= M` MP_TAC THENL
     [ASM_SIMP_TAC[]; INT_ARITH_TAC]]);;

let ijoin = new_definition
 `ijoin t (u:num->int) (v:num->int) =
    (\i. if i IN 1..t then u i else if i IN (t+1)..(2*t) then v(i - t) else
     &0)`;;

let ihead = new_definition `ihead t (w:num->int) = (\i. if i IN 1..t then w i
 else &0)`;;

let itail = new_definition `itail t (w:num->int) = (\i. if i IN 1..t then w(i +
 t) else &0)`;;

let IJOIN_IN = prove
 (`!t M (u:num->int) (v:num->int). u IN ibox t M /\
  v IN ibox t M ==> ijoin t u v IN ibox (2*t) M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
   REWRITE_TAC[ijoin] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THENL
   [REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_ABS_NUM; INT_LE_REFL] THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
       ASM_ARITH_TAC; ASM_ARITH_TAC];
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let IJOIN_INJ = prove
 (`!t M (u:num->int) v u' v'.
     1 <= t /\ u IN ibox t M /\ v IN ibox t M /\ u' IN ibox t M /\
      v' IN ibox t M /\
     ijoin t u v = ijoin t u' v'
     ==> u = u' /\ v = v'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ijoin; FUN_EQ_THM]) THEN
  DISCH_TAC THEN CONJ_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN
   X_GEN_TAC `i:num` THENL
   [ASM_CASES_TAC `i IN 1..t` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ASM_CASES_TAC `i IN 1..t` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `i + t`) THEN
      SUBGOAL_THEN `~((i + t) IN 1..t) /\ (i + t) IN (t+1)..(2*t) /\
       (i + t) - t = i` MP_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
        REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]]]);;

let IHEAD_IN = prove
 (`!t M (w:num->int). w IN ibox (2*t) M ==> ihead t w IN ibox t M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[ihead] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let ITAIL_IN = prove
 (`!t M (w:num->int). w IN ibox (2*t) M ==> itail t w IN ibox t M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[itail] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let IJOIN_HEADTAIL = prove
 (`!t M (w:num->int). w IN ibox (2*t) M ==> ijoin t (ihead t w) (itail t w) =
  w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[ijoin; ihead; itail; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
   REWRITE_TAC[IN_NUMSEG] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `1 <= i - t /\ i - t <= t` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let IPOLY1 = prove
 (`!f z:int. ipoly f 1 z = f 0 + f 1 * z`,
  REWRITE_TAC[ipoly] THEN SIMP_TAC[ISUM_CLAUSES_LEFT; LE_0] THEN
  REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; ISUM_SING_NUMSEG; INT_POW; INT_POW_1;
    INT_MUL_RID]);;

let ISUM_12 = prove
 (`!g:num->int. isum(1..2) g = g 1 + g 2`,
  GEN_TAC THEN MP_TAC(ISPECL [`g:num->int`; `1`; `2`] ISUM_CLAUSES_LEFT) THEN
  REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
   REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN
  MP_TAC(ISPECL [`g:num->int`; `2`; `2`] ISUM_CLAUSES_LEFT) THEN
   REWRITE_TAC[LE_REFL] THEN
  DISCH_THEN SUBST1_TAC THEN SUBGOAL_THEN `(2 + 1..2) = {}` SUBST1_TAC THENL
   [REWRITE_TAC[NUMSEG_EMPTY] THEN ARITH_TAC; REWRITE_TAC[ISUM_CLAUSES] THEN
    INT_ARITH_TAC]);;

let ABS_SEG_FINITE = prove
 (`!P:int. FINITE {v:int | abs v <= P}`,
  GEN_TAC THEN
   SUBGOAL_THEN `{v:int | abs v <= P} = {v:int | --P <= v /\
    v <= P}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN GEN_TAC THEN
    INT_ARITH_TAC; REWRITE_TAC[FINITE_INT_SEG]]);;

let ABS_SEG_CARD_LE = prove
 (`!P:int. &1 <= P ==> &(CARD {v:int | abs v <= P}) <= &3 * P`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:int | abs v <= P} = {x:int | --P <= x /\ x <= P}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[EXACT_INT_INTERVAL_CARD; INT_ARITH
   `&1 <= P ==> --P:int <= P`] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH
   `&1 <= P ==> &0:int <= P - --P + &1`] THEN
  ASM_INT_ARITH_TAC);;

let reparam = new_definition
  `reparam kk (w:num->int) =
     (\i. if i IN 1..kk then w(i+kk)
          else if i IN (kk+1)..(2*kk) then w(i-kk) - w(i) else &0)`;;

let ISUM_TAILSHIFT = prove
 (`!kk (g:num->int). isum((kk+1)..(2*kk)) g = isum(1..kk)(\i. g(i+kk))`,
  REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`kk:num`; `g:num->int`; `1`; `kk:num`] ISUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + kk = kk + 1`; ARITH_RULE `kk + kk = 2 * kk`] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let REPARAM_IN = prove
 (`!kk P (w:num->int). 1 <= kk /\
  w IN ibox (2*kk) P ==> reparam kk w IN ibox (2*kk) (&2 * P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM; reparam] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (P:int)` ASSUME_TAC THENL
   [SUBGOAL_THEN `abs((w:num->int)(1+kk)) <= P` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC; INT_ARITH_TAC]; ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_ABS_NUM] THEN
   RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
  TRY(SUBGOAL_THEN `abs((w:num->int)(i+kk)) <= P` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC; INT_ARITH_TAC]) THEN
  TRY(SUBGOAL_THEN `abs((w:num->int)(i-kk)) <= P /\
   abs((w:num->int) i) <= P` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC; INT_ARITH_TAC]) THEN
  (ASM_INT_ARITH_TAC ORELSE ASM_ARITH_TAC));;

let REPARAM_INJ = prove
 (`!kk P (w:num->int) w'.
     1 <= kk /\ w IN ibox (2*kk) P /\ w' IN ibox (2*kk) P /\
      reparam kk w = reparam kk w'
     ==> w = w'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[reparam; FUN_EQ_THM]) THEN DISCH_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i IN 1..2*kk` THENL
   [POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `i <= kk` THENL
     [FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i+kk`) THEN
      REWRITE_TAC[IN_NUMSEG] THEN
      SUBGOAL_THEN `(1 <= i /\ i <= kk /\ ~(1 <= i+kk /\ i+kk <= kk) /\
       (kk+1 <= i+kk /\ i+kk <= 2*kk) /\ (i+kk)-kk = i):bool` MP_TAC THENL
       [UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `i <= kk` THEN
        UNDISCH_TAC `1 <= kk` THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i-kk`) THEN REWRITE_TAC[IN_NUMSEG] THEN
      SUBGOAL_THEN `(1 <= i-kk /\ i-kk <= kk /\
       (i-kk)+kk = i):bool` MP_TAC THENL
       [UNDISCH_TAC `i <= 2*kk` THEN UNDISCH_TAC `~(i <= kk)` THEN
        UNDISCH_TAC `1 <= kk` THEN ARITH_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

let boxtuples = new_definition
 `boxtuples s P =
    {t | (!i. i IN 1..s ==> (t:num->num) i < P) /\
     (!i. ~(i IN 1..s) ==> t i = 0)}`;;

let boxsum = new_definition
 `boxsum e s (t:num->num) = nsum(1..s) (\i. (t i) EXP e)`;;

let rcount = new_definition
 `rcount e s P m = CARD {t | t IN boxtuples s P /\ boxsum e s t = m}`;;

let BOXTUPLES_FINITE = prove
 (`!s P. FINITE(boxtuples s P)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[boxtuples] THEN
   MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{f:num->num | (!x. x IN 1..s ==> f x IN {y | y < P}) /\
   (!x. ~(x IN 1..s) ==> f x = 0)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_FUNSPACE THEN
    REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT];
    REWRITE_TAC[SUBSET; IN_ELIM_THM]]);;

let monom = new_definition `monom e = \i:num. if i = e then &1:int else &0`;;

let IPOLY_MONOM = prove
 (`!e z:int. ipoly (monom e) e z = z pow e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ipoly; monom] THEN
  SUBGOAL_THEN `(\i. (if i = e then &1:int else &0) * z pow i) = (\i. if i = e
   then z pow e else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
    ASM_REWRITE_TAC[INT_MUL_LID; INT_MUL_LZERO]; ALL_TAC] THEN
  SIMP_TAC[ISUM_DELTA; IN_NUMSEG; LE_0; LE_REFL]);;

let RCOUNT_LE_SYM = prove
 (`!e s P m. 1 <= P
    ==> rcount e s P m <= CARD {x | x IN ibox s (&P) /\
     isum(1..s)(\i. ipoly (monom e) e (x i)) = &m}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[rcount] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\t:num->num. (\i. &(t i)):num->int) {t | t IN
   boxtuples s P /\ boxsum e s t = m})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`t1:num->num`;`t2:num->num`] THEN STRIP_TAC THEN
      POP_ASSUM MP_TAC THEN REWRITE_TAC[FUN_EQ_THM; INT_OF_NUM_EQ] THEN
       REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `boxtuples s P` THEN
       REWRITE_TAC[BOXTUPLES_FINITE] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox s (&P)` THEN
     REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:num->int` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM; boxtuples; boxsum]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ibox; IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THENL
     [REWRITE_TAC[INT_ABS_NUM; INT_OF_NUM_LE] THEN
      SUBGOAL_THEN `(t:num->num) i < P` MP_TAC THENL
       [ASM_MESON_TAC[]; ARITH_TAC];
      REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IPOLY_MONOM; INT_OF_NUM_POW; GSYM REAL_OF_NUM_ISUM_NUMSEG] THEN
     ASM_REWRITE_TAC[INT_OF_NUM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Leaf-index combinatorics: CHQ/CHSG/LEAFIDX/LEAFSG/RIFFLE/TSET etc.        *)
(* ------------------------------------------------------------------------- *)

let CHQ = new_definition
  `CHQ (t:num) (p:num->num) (b:bool) =
   \i. p((if i <= t then i else i-t) + (if b then t else 0))`;;

let CHSG = new_definition
  `CHSG (t:num) = \i:num. ~(i <= t)`;;

let LEAFIDX = new_recursive_definition num_RECURSION
  `(leafidx 0 t (pp:num->num->num) (bp:num->bool) = (\i:num. i)) /\
   (leafidx (SUC s) t pp bp =
      \i. CHQ t (pp 0) (bp 0) (leafidx s t (\j. pp(j+1)) (\j. bp(j+1)) i))`;;

let LEAFSG = new_recursive_definition num_RECURSION
  `(leafsg 0 t (pp:num->num->num) (bp:num->bool) = (\i:num. F)) /\
   (leafsg (SUC s) t pp bp =
      \i. ~(leafsg s t (\j. pp(j+1)) (\j. bp(j+1)) i <=>
            CHSG t (leafidx s t (\j. pp(j+1)) (\j. bp(j+1)) i)))`;;

let RIFFLE = new_definition
  `RIFFLE (t:num) =
   \x:num. if x IN 1..2*t then (if ODD x then (x+1) DIV 2 else t + x DIV 2)
    else x`;;

let TSET = new_definition
  `TSET (e:num) (G:num) = (1..e) UNION (IMAGE (\g. e*G + g) (1..e))`;;

let RIFFLE_PERMUTES = prove
 (`!t. RIFFLE t permutes 1..2*t`,
  GEN_TAC THEN SIMP_TAC[PERMUTES_FINITE_SURJECTIVE; FINITE_NUMSEG] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[RIFFLE];
    X_GEN_TAC `x:num` THEN REWRITE_TAC[RIFFLE] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN COND_CASES_TAC THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num`
      SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS]) THEN
      SUBGOAL_THEN `(SUC(2*m)+1) DIV 2 = m+1` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:num` SUBST_ALL_TAC o
        REWRITE_RULE[EVEN_EXISTS] o REWRITE_RULE[NOT_ODD]) THEN
      SUBGOAL_THEN `(2*m) DIV 2 = m` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC];
    X_GEN_TAC `y:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    ASM_CASES_TAC `y:num <= t` THENL
     [EXISTS_TAC `2*y-1` THEN REWRITE_TAC[RIFFLE; IN_NUMSEG] THEN
      SUBGOAL_THEN `ODD(2*y-1) /\ 1 <= 2*y-1 /\ 2*y-1 <= 2*t /\
       (2*y-1+1) DIV 2 = y`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[ODD_SUB; ODD_MULT; ARITH] THEN ASM_ARITH_TAC;
          ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC]; ASM_REWRITE_TAC[]];
      EXISTS_TAC `2*(y-t)` THEN REWRITE_TAC[RIFFLE; IN_NUMSEG] THEN
      SUBGOAL_THEN `~ODD(2*(y-t)) /\ 1 <= 2*(y-t) /\ 2*(y-t) <= 2*t /\
       t + (2*(y-t)) DIV 2 = y`
        STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[NOT_ODD; EVEN_MULT; ARITH]; ASM_ARITH_TAC; ASM_ARITH_TAC;
           ASM_ARITH_TAC];
        ASM_REWRITE_TAC[]]]]);;

let RIFFLE_VAL = prove
 (`!t m. 1 <= m /\ 2*m <= 2*t ==> RIFFLE t (2*m-1) = m /\
  RIFFLE t (2*m) = t + m`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RIFFLE] THEN
  (COND_CASES_TAC THENL
    [ALL_TAC;
     FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC]) THEN
  ASM_SIMP_TAC[ODD_SUB; ODD_MULT; ARITH; ODD; NOT_ODD; EVEN_MULT] THENL
   [SUBGOAL_THEN `(2*m-1+1) DIV 2 = m` (fun th->REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `(2*m) DIV 2 = m` (fun th->REWRITE_TAC[th]) THEN ARITH_TAC]);;

let RIFFLE_INJ = prove
 (`!t x y. RIFFLE t x = RIFFLE t y <=> x = y`,
  GEN_TAC THEN
   ACCEPT_TAC(MATCH_MP PERMUTES_INJECTIVE (SPEC `t:num` RIFFLE_PERMUTES)));;

let BLK = new_definition `BLK (B:num) (t:num) = (1..B) UNION (IMAGE (\j. t+j)
 (1..B))`;;

let IN_BLK = prove
 (`!B t x. x IN BLK B t <=> (1 <= x /\ x <= B) \/ (?j. 1 <= j /\ j <= B /\
  x = t+j)`,
  REWRITE_TAC[BLK; IN_UNION; IN_IMAGE; IN_NUMSEG] THEN MESON_TAC[]);;

let BLK_FULL = prove
 (`!B. BLK B B = 1..2*B`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_BLK; IN_NUMSEG] THEN
   X_GEN_TAC `x:num` THEN
  EQ_TAC THEN STRIP_TAC THENL
   [ASM_ARITH_TAC; ASM_ARITH_TAC;
    ASM_CASES_TAC `x:num <= B` THENL
     [DISJ1_TAC THEN ASM_ARITH_TAC; DISJ2_TAC THEN EXISTS_TAC `x - B:num` THEN
      ASM_ARITH_TAC]]);;

let TSET_EQ_BLK = prove
 (`!e G. TSET e G = BLK e (e*G)`,
  REWRITE_TAC[TSET; BLK]);;

let RIFFLE_BLK = prove
 (`!t B. EVEN B /\ 1 <= B /\
  B <= t ==> IMAGE (RIFFLE t) (1..B) = BLK (B DIV 2) t`,
  REPEAT STRIP_TAC THEN
   FIRST_X_ASSUM(X_CHOOSE_THEN `c:num`
    SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
  SUBGOAL_THEN `(2*c) DIV 2 = c` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_NUMSEG; IN_BLK] THEN
   X_GEN_TAC `v:num` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))
    THEN
    DISJ_CASES_TAC(SPEC `x:num` EVEN_OR_ODD) THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `m:num`
      SUBST_ALL_TAC o REWRITE_RULE[EVEN_EXISTS]) THEN
      DISJ2_TAC THEN EXISTS_TAC `m:num` THEN
      SUBGOAL_THEN `RIFFLE t (2*m) = t + m` SUBST1_TAC THENL
       [MP_TAC(SPECL [`t:num`;`m:num`] RIFFLE_VAL) THEN
        ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(X_CHOOSE_THEN `m:num`
       SUBST_ALL_TAC o REWRITE_RULE[ODD_EXISTS]) THEN
      DISJ1_TAC THEN
      SUBGOAL_THEN `RIFFLE t (SUC(2*m)) = m + 1` SUBST1_TAC THENL
       [MP_TAC(SPECL [`t:num`;`m+1`] RIFFLE_VAL) THEN
        REWRITE_TAC[ARITH_RULE `2*(m+1)-1 = SUC(2*m)`] THEN
         ASM_ARITH_TAC; ALL_TAC] THEN ASM_ARITH_TAC];
    STRIP_TAC THENL
     [EXISTS_TAC `2*v-1` THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`t:num`;`v:num`] RIFFLE_VAL) THEN
        ASM_ARITH_TAC; ASM_ARITH_TAC];
      EXISTS_TAC `2*j` THEN CONJ_TAC THENL
       [MP_TAC(SPECL [`t:num`;`j:num`] RIFFLE_VAL) THEN
        ASM_ARITH_TAC; ASM_ARITH_TAC]]]);;

let FF = new_definition
  `FF (t:num) = \y:num. RIFFLE t (if y <= t then y else y - t)`;;

let LEAFIDX_FF_REC = prove
 (`!s t i. leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i =
             RIFFLE t (if leafidx s t (\j:num. RIFFLE t) (\j:num. F) i <= t
                       then leafidx s t (\j:num. RIFFLE t) (\j:num. F) i
                       else leafidx s t (\j:num. RIFFLE t) (\j:num. F) i - t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LEAFIDX; CHQ] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES]);;

let LEAFIDX_FF = prove
 (`!s t i. leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i =
             FF t (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i)`,
  REWRITE_TAC[FF; LEAFIDX_FF_REC]);;

let FF_PAIR = prove
 (`!t w. 1 <= w /\ w <= t ==> FF t w = RIFFLE t w /\
  FF t (t + w) = RIFFLE t w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FF] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THENL
   [ASM_SIMP_TAC[ARITH_RULE `w <= t ==> (if w <= t then w else w - t) = w`];
    ASM_SIMP_TAC[ARITH_RULE `1 <= w ==> (if t + w <= t then t + w else (t + w)
     - t) = w`]]);;

let FF_BLK_IMAGE = prove
 (`!t C. 1 <= C /\
  C <= t ==> IMAGE (FF t) (BLK C t) = IMAGE (RIFFLE t) (1..C)`,
  REPEAT STRIP_TAC THEN
   REWRITE_TAC[EXTENSION; IN_IMAGE; IN_BLK; IN_NUMSEG] THEN
  X_GEN_TAC `v:num` THEN EQ_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `x:num` (CONJUNCTS_THEN2 SUBST1_TAC
   STRIP_ASSUME_TAC)) THENL
   [EXISTS_TAC `x:num` THEN MP_TAC(SPECL [`t:num`;`x:num`] FF_PAIR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[];
    EXISTS_TAC `j:num` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPECL [`t:num`;`j:num`] FF_PAIR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[];
    EXISTS_TAC `x:num` THEN MP_TAC(SPECL [`t:num`;`x:num`] FF_PAIR) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
     ASM_REWRITE_TAC[]]);;

let FF_FIBRE_EQ = prove
 (`!t B w y. 1 <= w /\ w <= 2*B /\ 2*B <= t /\ y IN BLK (2*B) t
            ==> (FF t y = RIFFLE t w <=> (y = w \/ y = t + w))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BLK] THEN STRIP_TAC THEN
  REWRITE_TAC[FF] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[RIFFLE_INJ] THEN ASM_ARITH_TAC);;

let BLK_RIFFLE_PREIMAGE = prove
 (`!t B v. 1 <= B /\ 2*B <= t /\ v IN BLK B t
           ==> ?w. 1 <= w /\ w <= 2*B /\ v = RIFFLE t w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_BLK] THEN STRIP_TAC THENL
   [EXISTS_TAC `2*v-1` THEN MP_TAC(SPECL [`t:num`;`v:num`] RIFFLE_VAL) THEN
    ASM_ARITH_TAC;
    EXISTS_TAC `2*j` THEN MP_TAC(SPECL [`t:num`;`j:num`] RIFFLE_VAL) THEN
     ASM_ARITH_TAC]);;

let TWOB_FACTS = prove
 (`!s t B. t = B * 2 EXP SUC s
           ==> t = (2*B) * 2 EXP s /\ (1 <= B ==> (1 <= 2*B /\ 2*B <= t /\
            EVEN(2*B)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXP] THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= 2 EXP s` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`; EXP_LT_0; ARITH]; ALL_TAC] THEN
  SUBGOAL_THEN `t = (2*B) * 2 EXP s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN REWRITE_TAC[EVEN_MULT; ARITH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `(2*B) * 1` THEN CONJ_TAC THENL
       [ARITH_TAC;
        GEN_REWRITE_TAC RAND_CONV [ASSUME `t = (2*B) * 2 EXP s`] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]]]);;

let T_BOUNDS = prove
 (`!B s t. t = (2*B)*2 EXP s /\ 1 <= B ==> 2*B <= t /\ 1 <= t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= 2 EXP s` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> 0 < n`; EXP_LT_0; ARITH]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `2*B = (2*B)*1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`; MULT_EQ_0; DE_MORGAN_THM;
      EXP_EQ_0] THEN
    ASM_ARITH_TAC]);;

let LEAFIDX_FF_IMAGE = prove
 (`!s t B. t = B * 2 EXP s /\ 1 <= B
          ==> IMAGE (leafidx s t (\j:num. RIFFLE t) (\j:num. F)) (1..2*t) = BLK
           B t`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [ASM_REWRITE_TAC[LEAFIDX; IMAGE_ID; EXP; MULT_CLAUSES; BLK_FULL];
     ALL_TAC] THEN
   SUBGOAL_THEN `IMAGE (leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F))
    (1..2*t) =
                IMAGE (FF t) (IMAGE (leafidx s t (\j:num. RIFFLE t) (\j:num.
                 F)) (1..2*t))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM; LEAFIDX_FF]; ALL_TAC] THEN
   MP_TAC(SPECL [`s:num`;`t:num`;`B:num`] TWOB_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
   ABBREV_TAC `T2 = B * 2 EXP SUC s` THEN
   SUBGOAL_THEN `IMAGE (leafidx s T2 (\j:num. RIFFLE T2) (\j:num. F)) (1..2*T2)
    = BLK (2*B) T2` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`T2:num`; `2*B:num`]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
       ASM_ARITH_TAC; ALL_TAC] THEN
   SUBGOAL_THEN `IMAGE (FF T2) (BLK (2*B) T2) = IMAGE (RIFFLE T2) (1..(2*B))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC FF_BLK_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `IMAGE (RIFFLE T2) (1..(2*B)) = BLK ((2*B) DIV 2) T2`
    SUBST1_TAC THENL
     [MATCH_MP_TAC RIFFLE_BLK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   REWRITE_TAC[ARITH_RULE `(2*B) DIV 2 = B`]);;

let LEAFIDX_FF_COUNT = prove
 (`!s t B v. t = B * 2 EXP s /\ 1 <= B /\ v IN BLK B t
           ==> {i | i IN 1..2*t /\
            leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = v} HAS_SIZE 2 EXP
             s`,
  INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `t:num = B` ASSUME_TAC THENL
     [ASM_MESON_TAC[EXP; MULT_CLAUSES]; ALL_TAC] THEN
    REWRITE_TAC[LEAFIDX; EXP] THEN
    SUBGOAL_THEN `1 <= v /\ v <= 2*B` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `v IN BLK B t` THEN UNDISCH_TAC `t:num = B` THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[BLK_FULL; IN_NUMSEG] THEN
       ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `{i | i IN 1..2*t /\ i = v} = {v}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_NUMSEG] THEN
      X_GEN_TAC `i:num` THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING]];
    ALL_TAC] THEN
   REPEAT GEN_TAC THEN STRIP_TAC THEN
   MP_TAC(SPECL [`s:num`;`t:num`;`B:num`] TWOB_FACTS) THEN
   ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
   MP_TAC(SPECL [`B:num`;`s:num`;`t:num`] T_BOUNDS) THEN
   ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
   MP_TAC(SPECL [`t:num`;`B:num`;`v:num`] BLK_RIFFLE_PREIMAGE) THEN
   ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
   UNDISCH_TAC `t = B * 2 EXP SUC s` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
   SUBGOAL_THEN `!i. i IN 1..2*t ==> leafidx s t (\j:num. RIFFLE t) (\j:num. F)
    i IN BLK (2*B) t`
    ASSUME_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MP_TAC(SPECL [`s:num`;`t:num`;`2*B:num`] LEAFIDX_FF_IMAGE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN
     `{i | i IN 1..2*t /\ leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i =
      v} =
      {i | i IN 1..2*t /\
       leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w} UNION
      {i | i IN 1..2*t /\
       leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w}`
     SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `i IN 1..2*t` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LEAFIDX_FF] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`t:num`;`B:num`;`w:num`;
                    `leafidx s t (\j:num. RIFFLE t) (\j:num. F) i`]
                     FF_FIBRE_EQ) THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
   SUBGOAL_THEN `2 EXP SUC s = 2 EXP s + 2 EXP s` SUBST1_TAC THENL
     [REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
   MATCH_MP_TAC HAS_SIZE_UNION THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `2*B:num`; `w:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_BLK] THEN DISJ1_TAC THEN
        ASM_ARITH_TAC; DISCH_THEN ACCEPT_TAC];
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `2*B:num`; `t+w:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_BLK] THEN DISJ2_TAC THEN EXISTS_TAC `w:num` THEN
        ASM_ARITH_TAC;
        DISCH_THEN ACCEPT_TAC];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM;
        NOT_IN_EMPTY] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      UNDISCH_TAC `leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LEAFIDX_FF_REGROUP = prove
 (`!e k (G:num).
    2 <= e /\ 1 <= G /\ G = 2 EXP k
    ==> IMAGE (leafidx k (e*G) (\j:num. RIFFLE (e*G)) (\j:num. F)) (1..2*e*G) =
     TSET e G /\
        (!g. g IN TSET e G
             ==> CARD {i | i IN 1..2*e*G /\
              leafidx k (e*G) (\j:num. RIFFLE (e*G)) (\j:num. F) i = g} = G)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `2*e*G = 2*(e*G)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e*G = e * 2 EXP k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL [`k:num`;`e*G:num`;`e:num`] LEAFIDX_FF_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[TSET_EQ_BLK] THEN DISCH_THEN ACCEPT_TAC;
    X_GEN_TAC `g:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`k:num`;`e*G:num`;`e:num`;`g:num`] LEAFIDX_FF_COUNT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; UNDISCH_TAC `g IN TSET e G` THEN
        REWRITE_TAC[TSET_EQ_BLK]];
      REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
    ASM_REWRITE_TAC[]]);;

let LEAFSG_FF_STEP = prove
 (`!s t i. leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i =
           ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i <=>
             CHSG t (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LEAFSG]);;

let LEAFSG_FF_SIGN_ON_FIBRE = prove
 (`!s t B w i. 1 <= w /\ w <= 2*B /\ 2*B <= t /\
               i IN 1..2*t /\
                leafidx s t (\j:num. RIFFLE t) (\j:num. F) i IN BLK (2*B) t
     ==> (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w
            ==> (leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i <=>
                 leafsg s t (\j:num. RIFFLE t) (\j:num. F) i))
      /\ (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w
            ==> (leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i <=>
                 ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LEAFSG_FF_STEP; CHSG] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `w <= t` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC TAUT;
    SUBGOAL_THEN `~(t + w <= t)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let LEAFSG_FF_FIBRE_SPLIT = prove
 (`!s t B w i. 1 <= w /\ w <= 2*B /\ 2*B <= t /\ i IN 1..2*t /\
               leafidx s t (\j:num. RIFFLE t) (\j:num. F) i IN BLK (2*B) t
     ==> ((leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i = RIFFLE t w /\
           ~(leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i)) <=>
          (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w /\
           ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i)) \/
          (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w /\
           leafsg s t (\j:num. RIFFLE t) (\j:num. F) i))
      /\ ((leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i = RIFFLE t w /\
           leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i) <=>
          (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w /\
           leafsg s t (\j:num. RIFFLE t) (\j:num. F) i) \/
          (leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w /\
           ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`t:num`;`B:num`;`w:num`;
                `leafidx s t (\j:num. RIFFLE t) (\j:num. F) i`] FF_FIBRE_EQ)
                 THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM LEAFIDX_FF] THEN DISCH_TAC THEN
  MP_TAC(SPECL [`s:num`;`t:num`;`B:num`;`w:num`;`i:num`]
   LEAFSG_FF_SIGN_ON_FIBRE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w /\
                  leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w)`
                   ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let TWOEXP_SUC_HALF = prove
 (`!s. 1 <= s ==> 2 EXP SUC s DIV 2 = 2 EXP s DIV 2 + 2 EXP s DIV 2`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. 2 EXP s = 2 * m` (CHOOSE_THEN (fun th -> ASSUME_TAC th))
   THENL
   [REWRITE_TAC[GSYM EVEN_EXISTS; EVEN_EXP] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[EXP; ARITH_RULE `2 * 2 * m = 2 * (2 * m)`] THEN
  SIMP_TAC[DIV_MULT; ARITH_EQ] THEN ARITH_TAC);;

let LEAFSG_FF_BALANCE = prove
 (`!s t B v. 1 <= s /\ t = B * 2 EXP s /\ 1 <= B /\ v IN BLK B t
     ==> {i | i IN 1..2*t /\
      leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = v /\
              ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i)} HAS_SIZE (2 EXP s
               DIV 2)
      /\ {i | i IN 1..2*t /\
       leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = v /\
              leafsg s t (\j:num. RIFFLE t) (\j:num. F) i} HAS_SIZE (2 EXP s
               DIV 2)`,
  INDUCT_TAC THENL [REWRITE_TAC[ARITH_RULE `~(1 <= 0)`]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`s:num`;`t:num`;`B:num`] TWOB_FACTS) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
   STRIP_TAC THEN
  MP_TAC(SPECL [`B:num`;`s:num`;`t:num`] T_BOUNDS) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
   STRIP_TAC THEN
  MP_TAC(SPECL [`t:num`;`B:num`;`v:num`] BLK_RIFFLE_PREIMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `t = B * 2 EXP SUC s` THEN
   DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
  SUBGOAL_THEN `!i. i IN 1..2*t ==> leafidx s t (\j:num. RIFFLE t) (\j:num. F)
   i IN BLK (2*B) t`
   ASSUME_TAC THENL
    [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
     MP_TAC(SPECL [`s:num`;`t:num`;`2*B:num`] LEAFIDX_FF_IMAGE) THEN
     ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
     DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) then SUBST1_TAC th else NO_TAC) THEN
  SUBGOAL_THEN
    `{i | i IN 1..2*t /\ leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i =
     RIFFLE t w /\
          ~(leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i)} =
     {i | i IN 1..2*t /\ leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w /\
          ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i)} UNION
     {i | i IN 1..2*t /\
      leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w /\
          leafsg s t (\j:num. RIFFLE t) (\j:num. F) i}`
    ASSUME_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
     ASM_CASES_TAC `i IN 1..2*t` THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`s:num`;`t:num`;`B:num`;`w:num`;`i:num`]
      LEAFSG_FF_FIBRE_SPLIT) THEN
     ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
    `{i | i IN 1..2*t /\ leafidx (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i =
     RIFFLE t w /\
          leafsg (SUC s) t (\j:num. RIFFLE t) (\j:num. F) i} =
     {i | i IN 1..2*t /\ leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w /\
          leafsg s t (\j:num. RIFFLE t) (\j:num. F) i} UNION
     {i | i IN 1..2*t /\
      leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = t + w /\
          ~(leafsg s t (\j:num. RIFFLE t) (\j:num. F) i)}`
    ASSUME_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN
     ASM_CASES_TAC `i IN 1..2*t` THEN ASM_REWRITE_TAC[] THEN
     MP_TAC(SPECL [`s:num`;`t:num`;`B:num`;`w:num`;`i:num`]
      LEAFSG_FF_FIBRE_SPLIT) THEN
     ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(w = t + w)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `s = 0` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ONCE_ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[LEAFIDX; LEAFSG]) THEN
     REWRITE_TAC[LEAFIDX; LEAFSG] THEN
    REWRITE_TAC[EMPTY_GSPEC; UNION_EMPTY; EMPTY_UNION] THEN
    SUBGOAL_THEN `{i | i IN 1..2*t /\ i = w} = {w} /\ {i | i IN 1..2*t /\
     i = t + w} = {t + w}`
     (CONJUNCTS_THEN SUBST1_TAC) THENL
     [CONJ_TAC THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; IN_NUMSEG] THEN
      X_GEN_TAC `j:num` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[HAS_SIZE; FINITE_SING; CARD_SING] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= s` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `w IN BLK (2*B) t /\
   (t + w) IN BLK (2*B) t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BLK] THEN CONJ_TAC THENL
     [DISJ1_TAC THEN ASM_ARITH_TAC;
      DISJ2_TAC THEN EXISTS_TAC `w:num` THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_SIMP_TAC[TWOEXP_SUC_HALF] THEN ONCE_ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC HAS_SIZE_UNION THEN
  FIRST_ASSUM(fun th -> if concl th = `t = (2 * B) * 2 EXP s` then
   REWRITE_TAC[SYM th] else NO_TAC) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `2*B:num`; `w:num`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `2*B:num`; `t+w:num`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `2*B:num`; `w:num`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`t:num`; `2*B:num`; `t+w:num`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `leafidx s t (\j:num. RIFFLE t) (\j:num. F) i = w` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let LEAFSG_FF_REGROUP = prove
 (`!e k (G:num).
    2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k
    ==> (!g. g IN TSET e G
             ==> CARD {i | i IN 1..2*e*G /\
              leafidx k (e*G) (\j:num. RIFFLE (e*G)) (\j:num. F) i = g /\
                           ~(leafsg k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F)
                            i)} = G DIV 2 /\
                 CARD {i | i IN 1..2*e*G /\
                  leafidx k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F) i = g /\
                           leafsg k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F) i}
                            = G DIV 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `2*e*G = 2*(e*G)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `e*G = e * 2 EXP k` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `g:num` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`k:num`;`e*G:num`;`e:num`;`g:num`] LEAFSG_FF_BALANCE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      UNDISCH_TAC `g IN TSET e G` THEN REWRITE_TAC[TSET_EQ_BLK] THEN
      ASM_MESON_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[HAS_SIZE] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[]);;

let LEAFIDX_REGROUP_RESIDUAL_FF_CLEAN = prove
 (`!e k (G:num).
    2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k
    ==> (IMAGE (leafidx k (e*G) (\j:num. RIFFLE (e*G)) (\j:num. F)) (1..2*e*G)
     = TSET e G /\
         (!g. g IN TSET e G
              ==> CARD {i | i IN 1..2*e*G /\
               leafidx k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F) i = g} = G))
                /\
        (!g. g IN TSET e G
             ==> CARD {i | i IN 1..2*e*G /\
              leafidx k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F) i = g /\
                           ~(leafsg k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F)
                            i)} = G DIV 2 /\
                 CARD {i | i IN 1..2*e*G /\
                  leafidx k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F) i = g /\
                           leafsg k (e*G) (\j:num. RIFFLE(e*G)) (\j:num. F) i}
                            = G DIV 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MP_TAC(SPECL [`e:num`;`k:num`;`G:num`] LEAFIDX_FF_REGROUP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    MP_TAC(SPECL [`e:num`;`k:num`;`G:num`] LEAFSG_FF_REGROUP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]);;

let jsplit = new_definition
 `jsplit p t (u:num->int) (v:num->int) =
    (\i. if i IN 1..p then u i else if i IN (p+1)..(p+t) then v(i - p) else
     &0)`;;

let jtl = new_definition `jtl p t (w:num->int) = (\i. if i IN 1..t then w(i +
 p) else &0)`;;

let IHEAD_IN_ADD = prove
 (`!p t M (w:num->int). w IN ibox (p+t) M ==> ihead p w IN ibox p M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[ihead] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let JTL_IN = prove
 (`!p t M (w:num->int). w IN ibox (p+t) M ==> jtl p t w IN ibox t M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[jtl] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
   ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let JSPLIT_IN = prove
 (`!p t M (u:num->int) (v:num->int). u IN ibox p M /\
  v IN ibox t M ==> jsplit p t u v IN ibox (p+t) M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
   REWRITE_TAC[jsplit] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_ABS_NUM; INT_LE_REFL]) THEN
  TRY(FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG]) THEN
   ASM_ARITH_TAC);;

let JSPLIT_HDTL = prove
 (`!p t M (w:num->int).
    w IN ibox (p+t) M ==> jsplit p t (ihead p w) (jtl p t w) = w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[jsplit; ihead; jtl; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
   REWRITE_TAC[IN_NUMSEG] THEN
  COND_CASES_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [SUBGOAL_THEN `1 <= i - p /\ i - p <= t` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC);;

let JSPLIT_INJ = prove
 (`!p t M (u:num->int) v u' v'.
     u IN ibox p M /\ v IN ibox t M /\ u' IN ibox p M /\ v' IN ibox t M /\
     jsplit p t u v = jsplit p t u' v'
     ==> u = u' /\ v = v'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "EQ" o REWRITE_RULE[jsplit; FUN_EQ_THM]) THEN
  CONJ_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THENL
   [ASM_CASES_TAC `i IN 1..p` THENL
     [REMOVE_THEN "EQ" (MP_TAC o SPEC `i:num`) THEN
      ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    ASM_CASES_TAC `i IN 1..t` THENL
     [SUBGOAL_THEN `~((i + p) IN 1..p) /\ (i + p) IN (p+1)..(p+t) /\
      (i + p) - p = i` STRIP_ASSUME_TAC THENL
       [RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
        REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        REMOVE_THEN "EQ" (MP_TAC o SPEC `i + p:num`) THEN ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[]]]);;

let TAIL_ISUM_JTL = prove
 (`!p t (w:num->int) (W:num->int->int). isum((p+1)..(p+t))(\i. W i (w i)) =
  isum(1..t)(\i. W (i+p) (jtl p t w i))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  MP_TAC(ISPECL [`p:num`; `\i. (W:num->int->int) i ((w:num->int) i)`; `1`;
    `t:num`] ISUM_OFFSET) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
   X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; jtl; IN_NUMSEG] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL
   [REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ARITH_TAC; ASM_ARITH_TAC]);;

let TAIL_ISUM_JSPLIT = prove
 (`!p t (u:num->int) (v:num->int) (W:num->int->int). isum((p+1)..(p+t))(\i. W i
  (jsplit p t u v i)) = isum(1..t)(\i. W (i+p) (v i))`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [ADD_SYM] THEN
  MP_TAC(ISPECL [`p:num`;
    `\i. (W:num->int->int) i (jsplit p t (u:num->int) (v:num->int) i)`; `1`;
      `t:num`] ISUM_OFFSET) THEN
  BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
   X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; jsplit; IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(1 <= i+p /\ i+p <= p) /\ (p+1 <= i+p /\ i+p <= p+t) /\
   (i+p)-p = i` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]);;

let IBOX_0 = prove
 (`!M. ibox 0 M = {(\i. &0)}`,
  GEN_TAC THEN REWRITE_TAC[ibox] THEN
  SUBGOAL_THEN `1..0 = {}` SUBST1_TAC THENL [REWRITE_TAC[NUMSEG_EMPTY] THEN
   ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[NOT_IN_EMPTY; EXTENSION; IN_ELIM_THM] THEN
   REWRITE_TAC[IN_SING; FUN_EQ_THM]);;

let LASTBLOCK_ISUM = prove
 (`!(Vm:num->int->int) p t (w:num->int).
     isum((p+1)..(p+t))(\i. Vm (i-p) (w i)) = isum(1..t)(\i. Vm i (w (p+i)))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `(p+1)..(p+t) = (1+p)..(t+p)` SUBST1_TAC THENL
   [REWRITE_TAC[ADD_SYM]; ALL_TAC] THEN
  REWRITE_TAC[ISUM_OFFSET] THEN BETA_TAC THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `(i + p) - p = i /\
   (p:num) + i = i + p` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ARITH_TAC; REWRITE_TAC[]]);;

let BLOCK_PEEL_CARD = prove
 (`!(Q:(num->int)->bool) (W:num->int->int) p t M b.
    (!u v. u IN ibox p M /\ v IN ibox t M ==> (Q (jsplit p t u v) <=> Q u))
    ==> CARD {w | w IN ibox (p+t) M /\ Q w /\
     isum((p+1)..(p+t))(\i. W i (w i)) = b} =
        CARD {u | u IN ibox p M /\ Q u} *
        CARD {v | v IN ibox t M /\ isum(1..t)(\i. W (i+p) (v i)) = b}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{w:num->int | w IN ibox (p+t) M /\ Q w /\
    isum((p+1)..(p+t))(\i. (W:num->int->int) i (w i)) = b} =
    IMAGE (\pr. jsplit p t (FST pr) (SND pr))
          (({u:num->int | u IN ibox p M /\ Q u}) CROSS
           ({v:num->int | v IN ibox t M /\
            isum(1..t)(\i. W (i+p) (v i)) = b}))`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM;
     IN_CROSS] THEN
    X_GEN_TAC `w:num->int` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC
       [`ihead p (w:num->int)`; `jtl p t (w:num->int)`] THEN
      SUBGOAL_THEN `ihead p (w:num->int) IN ibox p M /\
       jtl p t (w:num->int) IN ibox t M` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[IHEAD_IN_ADD; JTL_IN]; ALL_TAC] THEN
      SUBGOAL_THEN `jsplit p t (ihead p (w:num->int)) (jtl p t w) = w`
       ASSUME_TAC THENL
       [ASM_MESON_TAC[JSPLIT_HDTL]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[];
        MATCH_MP_TAC IHEAD_IN_ADD THEN EXISTS_TAC `t:num` THEN
         ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        MATCH_MP_TAC JTL_IN THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[GSYM TAIL_ISUM_JTL] THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC JSPLIT_IN THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        REWRITE_TAC[TAIL_ISUM_JSPLIT] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ({u:num->int | u IN ibox p M /\ Q u}) /\
   FINITE ({v:num->int | v IN ibox t M /\
    isum(1..t)(\i. (W:num->int->int) (i+p) (v i)) = b})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THENL
     [EXISTS_TAC `ibox p M`; EXISTS_TAC `ibox t M`] THEN
      REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\pr. jsplit p t (FST pr) (SND pr:num->int)`;
    `({u:num->int | u IN ibox p M /\ Q u} CROSS {v:num->int | v IN ibox t M /\
     isum(1..t)(\i. (W:num->int->int) (i+p) (v i)) = b})`] CARD_IMAGE_INJ) THEN
  ASM_SIMP_TAC[FINITE_CROSS] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`u1:num->int`;`v1:num->int`;`u2:num->int`;`v2:num->int`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC JSPLIT_INJ THEN
     MAP_EVERY EXISTS_TAC [`p:num`; `t:num`; `M:int`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CARD_CROSS]]);;

let JSPLIT_COORD_LO = prove
 (`!m t (u:num->int) (v:num->int) g i. g < m /\ 1 <= i /\ i <= t
     ==> jsplit (m*t) t u v (g*t+i) = u (g*t+i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(g*t+i) IN 1..(m*t)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `g*t + t:num` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC;
        REWRITE_TAC[ARITH_RULE `g*t + t = (g+1)*t`; LE_MULT_RCANCEL] THEN
         DISJ1_TAC THEN ASM_ARITH_TAC]];
    ALL_TAC] THEN
  REWRITE_TAC[jsplit] THEN ASM_REWRITE_TAC[]);;

let BLOCKSUM_JSPLIT = prove
 (`!(V:num->num->int->int) t m (u:num->int) (v:num->int) g. g < m
     ==> isum(1..t)(\i. V g i (jsplit (m*t) t u v (g*t+i))) = isum(1..t)(\i. V
      g i (u (g*t+i)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
   REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  AP_TERM_TAC THEN MATCH_MP_TAC JSPLIT_COORD_LO THEN ASM_REWRITE_TAC[]);;

let HEAD_PRED_INV = prove
 (`!(V:num->num->int->int) t (z:num->int) m (u:num->int) (v:num->int).
     ((!g. g < m ==> isum(1..t)(\i. V g i (jsplit (m*t) t u v (g*t+i))) = z g)
      <=>
      (!g. g < m ==> isum(1..t)(\i. V g i (u (g*t+i))) = z g))`,
  REPEAT GEN_TAC THEN EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `g:num` THEN
   DISCH_TAC THEN
  (MP_TAC(ISPECL
   [`V:num->num->int->int`;`t:num`;`m:num`;`u:num->int`;`v:num->int`;`g:num`]
    BLOCKSUM_JSPLIT) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
   FIRST_X_ASSUM(MP_TAC o SPEC `g:num`) THEN ASM_REWRITE_TAC[] THEN
    ASM_INT_ARITH_TAC));;

let MBLOCK_FIBER_CARD = prove
 (`!(V:num->num->int->int) t M (z:num->int) m.
    CARD {w | w IN ibox (m*t) M /\
     (!g. g < m ==> isum(1..t)(\i. V g i (w (g*t+i))) = z g)} =
    nproduct {g | g < m} (\g. CARD{ u | u IN ibox t M /\
     isum(1..t)(\i. V g i (u i)) = z g })`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; LT; EMPTY_GSPEC; NPRODUCT_CLAUSES; IBOX_0] THEN
    SUBGOAL_THEN `{w:num->int | w IN {(\i. &0)}} = {(\i. &0)}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; REWRITE_TAC[CARD_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC m * t = (m * t) + t` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `nproduct (m INSERT {g | g < m}) (\g. CARD{ u:num->int | u IN
   ibox t M /\
    isum(1..t)(\i. (V:num->num->int->int) g i (u i)) = (z:num->int) g }) =
    CARD{ u:num->int | u IN ibox t M /\ isum(1..t)(\i. V m i (u i)) = z m } *
    nproduct {g | g < m} (\g. CARD{ u:num->int | u IN ibox t M /\
     isum(1..t)(\i. V g i (u i)) = z g })`
   ASSUME_TAC THENL
   [SIMP_TAC[NPRODUCT_CLAUSES; FINITE_NUMSEG_LT] THEN
    COND_CASES_TAC THENL
     [POP_ASSUM MP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `{g | g < SUC m} = m INSERT {g | g < m}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_ELIM_THM] THEN
    ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `{w:num->int | w IN ibox ((m*t)+t) M /\
    (!g. g < SUC m ==> isum(1..t)(\i. (V:num->num->int->int) g i (w (g*t+i))) =
     (z:num->int) g)} =
    {w:num->int | w IN ibox ((m*t)+t) M /\
     (\ww. !g. g < m ==> isum(1..t)(\i. V g i (ww (g*t+i))) = z g) w /\
      isum(((m*t)+1)..((m*t)+t))(\i. V m (i-(m*t)) (w i)) = z m}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:num->int` THEN
    BETA_TAC THEN
    ASM_CASES_TAC `(w:num->int) IN ibox ((m*t)+t) M` THEN
     ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[LASTBLOCK_ISUM; LT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
    [`\ww:num->int. !g. g < m ==> isum(1..t)(\i. (V:num->num->int->int) g i (ww
     (g*t+i))) = (z:num->int) g`;
     `\i. (V:num->num->int->int) m (i-(m*t))`; `m*t:num`; `t:num`; `M:int`;
       `(z:num->int) m`]
    BLOCK_PEEL_CARD) THEN
  BETA_TAC THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:num->int`; `v:num->int`] THEN STRIP_TAC THEN
    REWRITE_TAC[HEAD_PRED_INV]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [MULT_SYM] THEN
  BINOP_TAC THENL [REFL_TAC; AP_TERM_TAC THEN REWRITE_TAC[ADD_SUB]]);;

let TSET_CARD = prove
 (`!e G. 1 <= G ==> CARD(TSET e G) = 2*e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[TSET] THEN
  SUBGOAL_THEN `e <= e*G` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `e = e*1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(1..e) INTER (IMAGE (\g. e*G + g) (1..e)) = {}`
   ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_NUMSEG; IN_IMAGE] THEN
    X_GEN_TAC `x:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_UNION; FINITE_NUMSEG; FINITE_IMAGE] THEN
  SUBGOAL_THEN `CARD(IMAGE (\g. e*G + g) (1..e)) = CARD(1..e)` SUBST1_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    ARITH_TAC;
    REWRITE_TAC[CARD_NUMSEG_1] THEN ARITH_TAC]);;

let FIBRE_HAS_SIZE_G = prove
 (`!e k (G:num) t. 2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k /\ t IN TSET e G
   ==> {i | i IN 1..2*e*G /\
    leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i = t} HAS_SIZE G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:num`; `e*G:num`; `e:num`; `t:num`] LEAFIDX_FF_COUNT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ONCE_ASM_REWRITE_TAC[] THEN REFL_TAC;
      ASM_ARITH_TAC;
      UNDISCH_TAC `t IN TSET e G` THEN REWRITE_TAC[TSET_EQ_BLK]];
    DISCH_THEN(fun th -> MP_TAC th) THEN
    FIRST_X_ASSUM(fun th -> if concl th = `G = 2 EXP k` then GEN_REWRITE_TAC
     (LAND_CONV o RAND_CONV) [SYM th] else NO_TAC) THEN
    REWRITE_TAC[]]);;

let LEAF_BLOCK_REINDEX = prove
 (`!e k (G:num). 2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k
   ==> ?lab. (!g. g < 2*e ==> lab g IN TSET e G) /\
             (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
             (!g. g < 2*e ==> ?en. (!r. r < G ==> en r IN {i | i IN 1..2*e*G /\
              leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g}) /\
                                   (!i. i IN {i | i IN 1..2*e*G /\
                                    leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i
                                     = lab g} ==> ?!r. r < G /\ en r = i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`TSET e G`; `2*e`] HAS_SIZE_INDEX) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [REWRITE_TAC[TSET] THEN
      SIMP_TAC[FINITE_UNION; FINITE_NUMSEG; FINITE_IMAGE];
      MATCH_MP_TAC TSET_CARD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `lab:num->num` (CONJUNCTS_THEN2 (LABEL_TAC "LAB")
   (LABEL_TAC "LABU"))) THEN
  EXISTS_TAC `lab:num->num` THEN
  CONJ_TAC THENL [REMOVE_THEN "LAB" ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REMOVE_THEN "LABU" ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `g:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{i | i IN 1..2*e*G /\
   leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i = (lab:num->num) g} HAS_SIZE G`
    MP_TAC THENL
   [MATCH_MP_TAC FIBRE_HAS_SIZE_G THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "LAB" (fun th -> MP_TAC(SPEC `g:num` th)) THEN
     ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP HAS_SIZE_INDEX) THEN MESON_TAC[]]);;

let SIGNED_FAM = new_definition
 `signfam (V:num->int->int) t =
  \i x. if i <= t then V i x else --(V (i-t) x)`;;

let CHILDFAM = new_definition
 `childfam (Wf:(num->int)->num->int->int) t (p:num->num) b =
    if b then (\hh. signfam (\j. Wf hh (p(j+t))) t)
         else (\hh. signfam (\k. Wf hh (p k)) t)`;;

let PLEAF = new_recursive_definition num_RECURSION
 `(pleaf 0 (Wf:(num->int)->num->int->int) t (pp:num->num->num) (bp:num->bool) =
  Wf) /\
  (pleaf (SUC s) (Wf:(num->int)->num->int->int) t (pp:num->num->num)
   (bp:num->bool) =
     pleaf s (childfam Wf t (pp 0) (bp 0)) t (\j:num. pp(j+1)) (\j:num.
      bp(j+1)))`;;

let SGNRELAB = new_definition
  `SGNRELAB (Wf:(num->int)->num->int->int) (sg:num->bool) (q:num->num) =
     \hh i x. if sg i then --(Wf hh (q i) x) else Wf hh (q i) x`;;

let CHILDFAM_SGNRELAB = prove
 (`!(Wf:(num->int)->num->int->int) t p b.
     childfam Wf t p b = SGNRELAB Wf (CHSG t) (CHQ t p b)`,
  REWRITE_TAC[CHILDFAM; SGNRELAB; SIGNED_FAM; CHSG; CHQ; FUN_EQ_THM] THEN
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES]);;

let SGNRELAB_COMPOSE = prove
 (`!(Wf:(num->int)->num->int->int) sg1 q1 sg2 q2.
     SGNRELAB (SGNRELAB Wf sg1 q1) sg2 q2 =
     SGNRELAB Wf (\i. ~(sg2 i <=> sg1(q2 i))) (\i. q1(q2 i))`,
  REWRITE_TAC[SGNRELAB; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_NEG_NEG]) THEN
   ASM_MESON_TAC[]);;

let SGNRELAB_ID = prove
 (`!(Wf:(num->int)->num->int->int). SGNRELAB Wf (\i. F) (\i. i) = Wf`,
  REWRITE_TAC[SGNRELAB; FUN_EQ_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]);;

let PLEAF_SGNRELAB = prove
 (`!s (Wf:(num->int)->num->int->int) t pp bp.
     pleaf s Wf t pp bp = SGNRELAB Wf (leafsg s t pp bp) (leafidx s t pp bp)`,
  INDUCT_TAC THENL
   [REWRITE_TAC[PLEAF; LEAFIDX; LEAFSG; SGNRELAB_ID]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[PLEAF] THEN
  FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
     MP_TAC(SPECL [`childfam (Wf:(num->int)->num->int->int) t (pp 0) (bp 0)`;
                   `t:num`; `\j:num. (pp:num->num->num)(j+1)`;
                     `\j:num. (bp:num->bool)(j+1)`] ih)
     else NO_TAC) THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CHILDFAM_SGNRELAB; SGNRELAB_COMPOSE] THEN
  REWRITE_TAC[LEAFIDX; LEAFSG] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[]);;

let LEAF_BLOCK_REINDEX_SK = prove
 (`!e k (G:num). 2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k
   ==> ?(lab:num->num) (en:num->num->num).
         (!g. g < 2*e ==> lab g IN TSET e G) /\
         (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
         (!g r. g < 2*e /\ r < G ==> en g r IN 1..2*e*G /\
          leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g r) = lab g) /\
         (!g i. g < 2*e /\ i IN 1..2*e*G /\
          leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g ==> ?!r. r < G /\
           en g r = i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`k:num`;`G:num`] LEAF_BLOCK_REINDEX) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lab:num->num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `lab:num->num` THEN
  FIRST_X_ASSUM(fun th -> if is_forall(concl th) && (let
   b=snd(strip_forall(concl th)) in is_imp b && (let (_,c)=dest_imp b in
    is_exists c)) then
     MP_TAC(REWRITE_RULE[RIGHT_IMP_EXISTS_THM;
       SKOLEM_THM] th) else NO_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `en:num->num->num`) THEN
   EXISTS_TAC `en:num->num->num` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`g:num`;`r:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `r:num` o CONJUNCT1) THEN
     ASM_REWRITE_TAC[IN_ELIM_THM];
    MAP_EVERY X_GEN_TAC [`g:num`;`i:num`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:num`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT2) THEN
     ASM_REWRITE_TAC[IN_ELIM_THM]]);;

let LEAFIDX_INTO_TSET = prove
 (`!e k (G:num) i. 2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k /\ i IN 1..2*e*G
     ==> leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i IN TSET e G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`k:num`;`G:num`] LEAFIDX_REGROUP_RESIDUAL_FF_CLEAN)
   THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN REWRITE_TAC[IN_IMAGE] THEN
  EXISTS_TAC `i:num` THEN
  CONJ_TAC THENL
   [REFL_TAC;
    FIRST_X_ASSUM(fun th -> if concl th = `G = 2 EXP k` then REWRITE_TAC[SYM
     th] else NO_TAC) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let LEAF_BLOCK_INJ = prove
 (`!e k (G:num) (lab:num->num) (en:num->num->num).
     2 <= e /\ e-1 <= k /\ 1 <= G /\ G = 2 EXP k /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
     (!g r. g < 2*e /\ r < G ==> en g r IN 1..2*e*G /\
      leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g r) = lab g) /\
     (!g i. g < 2*e /\ i IN 1..2*e*G /\
      leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g ==> ?!r. r < G /\
       en g r = i)
     ==> !g1 r1 g2 r2. g1 < 2*e /\ r1 < G /\ g2 < 2*e /\ r2 < G /\
      en g1 r1 = en g2 r2 ==> g1 = g2 /\ r1 = r2`,
  REPEAT GEN_TAC THEN INTRO_TAC "E1 EK G1 GEXP LABU EN ENU" THEN
  MAP_EVERY X_GEN_TAC [`g1:num`;`r1:num`;`g2:num`;`r2:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(en:num->num->num) g1 r1 IN 1..2*e*G /\
   leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g1 r1) = lab g1`
    (CONJUNCTS_THEN2 (LABEL_TAC "M1") (LABEL_TAC "L1")) THENL
   [USE_THEN "EN" (fun th -> MP_TAC(SPECL [`g1:num`;`r1:num`] th)) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `leafidx k (e*G) (\j. RIFFLE(e*G)) (\j. F) ((en:num->num->num)
   g2 r2) = lab g2`
    (LABEL_TAC "L2") THENL
   [USE_THEN "EN" (fun th -> MP_TAC(SPECL [`g2:num`;`r2:num`] th)) THEN
    ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(lab:num->num) g1 = lab g2` ASSUME_TAC THENL
   [USE_THEN "L1" (SUBST1_TAC o SYM) THEN USE_THEN "L2" (SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(lab:num->num) g1 IN TSET e G` ASSUME_TAC THENL
   [USE_THEN "L1" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC LEAFIDX_INTO_TSET THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `g1:num = g2` ASSUME_TAC THENL
   [USE_THEN "LABU" (fun th -> MP_TAC(SPEC `(lab:num->num) g1` th)) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    DISCH_THEN(fun th -> MP_TAC(SPECL [`g1:num`;`g2:num`] th)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "ENU" (fun th -> MP_TAC(SPECL [`g1:num`;`(en:num->num->num) g1 r1`]
   th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
   USE_THEN "L1" ACCEPT_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`r1:num`;`r2:num`] th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ONCE_ASM_REWRITE_TAC[] THEN
   REFL_TAC; SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Inner multiplicity helpers (FOUR_EXP_STEP, MFB_COEFF_BND)                 *)
(* ------------------------------------------------------------------------- *)

let FOUR_EXP_STEP = prove
 (`!e. &3 * &(4 EXP SUC e) + &1 <= &(4 EXP SUC(SUC e)):int`,
  GEN_TAC THEN
   REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD;
     GSYM INT_OF_NUM_LE] THEN
  SUBGOAL_THEN `4 EXP SUC(SUC e) = 4 * 4 EXP SUC e` SUBST1_TAC THENL
   [REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &(4 EXP SUC e):int` MP_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE; ARITH_RULE `1 <= n <=> ~(n=0)`; EXP_EQ_0] THEN
    ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC);;

let MFB_COEFF_BND = prove
 (`!e (g0:num->int) P h j. &1 <= P /\ abs h <= &2 * P /\ j <= SUC e /\
     (!k. k <= e ==> abs (g0 k) <= &(4 EXP SUC e) * P pow (e - k))
   ==> abs((if j = 0 then &0 else g0 (j - 1)) + (if j <= e then h * g0 j else
    &0) + (if j = SUC e then &1 else &0))
       <= &(4 EXP SUC(SUC e)) * P pow (SUC e - j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `abs(if j = 0 then &0 else (g0:num->int)(j-1)) + abs(if j <= e
   then h * g0 j else &0) + abs(if j = SUC e then &1 else &0)` THEN
  CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (P:int)` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (P:int) pow (SUC e - j)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (P:int) pow (SUC e - j)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE_1 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `abs(if j = 0 then &0 else (g0:num->int)(j-1)) <= &(4 EXP SUC e)
   * P pow (SUC e - j)` ASSUME_TAC THENL
   [COND_CASES_TAC THENL
     [REWRITE_TAC[INT_ABS_NUM] THEN MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
      [REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(j:num) - 1 <= e` ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC e - j = e - (j - 1)` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> (try fst(dest_forall(concl
       th))=`k:num` with _ -> false))) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs(if j <= e then h * (g0:num->int) j else &0) <= &2 * &(4 EXP
   SUC e) * P pow (SUC e - j)` ASSUME_TAC THENL
   [COND_CASES_TAC THENL
     [REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `(&2 * (P:int)) * &(4 EXP SUC e) * P pow (e - j)` THEN
       CONJ_TAC THENL
       [MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_ABS_POS] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> (try fst(dest_forall(concl
         th))=`k:num` with _ -> false))) THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN
         `(&2 * (P:int)) * &(4 EXP SUC e) * P pow (e - j) =
          &2 * &(4 EXP SUC e) * (P * P pow (e - j))`
         SUBST1_TAC THENL
          [INT_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN
         `(P:int) * P pow (e - j) = P pow (SUC e - j)`
         SUBST1_TAC THENL
         [REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN AP_TERM_TAC THEN
          ASM_ARITH_TAC; REWRITE_TAC[INT_LE_REFL]]];
      REWRITE_TAC[INT_ABS_NUM] THEN MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
       [INT_ARITH_TAC; MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
        [REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; ASM_REWRITE_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `abs(if j = SUC e then &1 else &0) <= (P:int) pow (SUC e - j)`
   ASSUME_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[INT_ABS_NUM] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `(&(4 EXP SUC e):int) * P pow (SUC e - j) +
    &2 * &(4 EXP SUC e) * P pow (SUC e - j) +
    P pow (SUC e - j)` THEN
  CONJ_TAC THENL [MATCH_MP_TAC INT_LE_ADD2 THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; MATCH_MP_TAC INT_LE_ADD2 THEN
    ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&(4 EXP SUC e):int) * P pow (SUC e - j) +
    &2 * &(4 EXP SUC e) * P pow (SUC e - j) +
    P pow (SUC e - j) =
    (&3 * &(4 EXP SUC e) + &1) * P pow (SUC e - j)`
   SUBST1_TAC THENL
   [INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[FOUR_EXP_STEP]);;

(* ------------------------------------------------------------------------- *)
(* Difference-polynomial fiber counts: the DPWIH2 induction, FUND_LEMMA_CF,  *)
(* the weak-multiplicity (_W) chain, and the Schnirelmann capstone           *)
(* (HILBERT_WARING).                                                         *)
(* ------------------------------------------------------------------------- *)

let LINCOUNT_TRANSLATE = prove
 (`!s:A->bool a m B. FINITE s /\ &0 <= B
    ==> lincount s a m B <= lincount s a (&0) (&2 * B)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `MS = {z:A->int | (!i. i IN s ==> abs(z i) <= B) /\
   (!i. ~(i IN s) ==> z i = &0) /\ isum s (\i. a i * z i) = m}` THEN
  SUBGOAL_THEN `FINITE (MS:(A->int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "MS" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= B) /\
     (!i. ~(i IN s) ==> a i = &0)}` THEN
    ASM_SIMP_TAC[COEFFBOX_FINITE] THEN EXPAND_TAC "MS" THEN
     REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `MS:(A->int)->bool = {}` THENL
   [EXPAND_TAC "MS" THEN REWRITE_TAC[lincount] THEN
    UNDISCH_TAC `MS:(A->int)->bool = {}` THEN EXPAND_TAC "MS" THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_CLAUSES; LE_0]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z0:A->int` MP_TAC) THEN EXPAND_TAC "MS" THEN
   REWRITE_TAC[IN_ELIM_THM] THEN
  STRIP_TAC THEN REWRITE_TAC[lincount] THEN
  FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) =
   `MS:(A->int)->bool` then REWRITE_TAC[th] else NO_TAC) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD (IMAGE (\z:A->int. \i. z i - z0 i) MS)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`u:A->int`;`v:A->int`] THEN
    REWRITE_TAC[FUN_EQ_THM] THEN STRIP_TAC THEN X_GEN_TAC `i:A` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A`) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `IMS = IMAGE (\z:A->int. \i. z i - z0 i) MS` THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [EXPAND_TAC "IMS" THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `w:A->int` THEN
    DISCH_THEN(X_CHOOSE_THEN `z:A->int` MP_TAC) THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) =
     `MS:(A->int)->bool` then REWRITE_TAC[GSYM th] else NO_TAC) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
     REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `abs((z:A->int) i) <= B /\
       abs((z0:A->int) i) <= B` MP_TAC THENL
       [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      X_GEN_TAC `i:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:A->int) i = &0 /\ (z0:A->int) i = &0` MP_TAC THENL
       [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      SUBGOAL_THEN `isum s (\i. (a:A->int) i * (z i - z0 i)) = isum s (\i. a i
       * z i) - isum s (\i. a i * z0 i)` SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM ISUM_SUB] THEN MATCH_MP_TAC ISUM_EQ THEN
        X_GEN_TAC `i:A` THEN DISCH_TAC THEN REWRITE_TAC[] THEN INT_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]];
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{a:A->int | (!i. i IN s ==> abs(a i) <= &2 * B) /\
     (!i. ~(i IN s) ==> a i = &0)}` THEN
    ASM_SIMP_TAC[COEFFBOX_FINITE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     SIMP_TAC[]]);;

let FAMILY_NONHOMOG_LE = prove
 (`!s:A->bool A B (mfn:(A->int)->int).
     FINITE s /\ &0 <= B
    ==> isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
     (!i. ~(i IN s) ==> a i = &0)}
             (\a. &(lincount s a (mfn a) B))
        <= isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
         (!i. ~(i IN s) ==> a i = &0)}
             (\a. &(lincount s a (&0) (&2 * B)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISUM_LE THEN
  ASM_SIMP_TAC[COEFFBOX_FINITE] THEN X_GEN_TAC `a:A->int` THEN DISCH_TAC THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN MATCH_MP_TAC LINCOUNT_TRANSLATE THEN
   ASM_REWRITE_TAC[]);;

let LEMMA3_HOMOG_FAMILY_1 = prove
 (`!s:A->bool. FINITE s /\ 2 < CARD s
    ==> ?c. !A B:int. &1 <= A /\ A <= B /\ B <= A pow (CARD s - 1)
            ==> isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
                                 (!i. ~(i IN s) ==> a i = &0)}
                     (\a. &(lincount s a (&0) B))
                <= c * (A * B) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:A->bool` NONZERO_FAMILY) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `Cnz:int`) THEN
  EXISTS_TAC `(&3:int) pow (CARD(s:A->bool)) * &1 + (Cnz:int)` THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A->bool`; `A:int`; `B:int`] FAMILY_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `((&3:int) pow (CARD(s:A->bool)) * &1) *
    ((A:int) * B) pow (CARD s - 1) +
    Cnz * (A * B) pow (CARD s - 1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_ADD2 THEN CONJ_TAC THENL
     [MATCH_MP_TAC ZEROTERM_FINAL THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `2 < CARD(s:A->bool)` THEN
       ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[INT_MUL_LID] THEN INT_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[INT_MUL_LID]];
    REWRITE_TAC[GSYM INT_ADD_RDISTRIB] THEN INT_ARITH_TAC]);;

let FAMILY_NONHOMOG_BND = prove
 (`!s:A->bool. FINITE s /\ 2 < CARD s
    ==> ?c. !A B (mfn:(A->int)->int). &1 <= A /\ A <= &2 * B /\
     &2 * B <= A pow (CARD s - 1)
            ==> isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
             (!i. ~(i IN s) ==> a i = &0)}
                     (\a. &(lincount s a (mfn a) B))
                <= c * (A * (&2 * B)) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:A->bool` LEMMA3_HOMOG_FAMILY_1) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `c:int`) THEN
  EXISTS_TAC `c:int` THEN
  MAP_EVERY X_GEN_TAC [`A:int`; `B:int`; `mfn:(A->int)->int`] THEN
   STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum {a:A->int | (!i. i IN s ==> abs(a i) <= A) /\
   (!i. ~(i IN s) ==> a i = &0)}
             (\a. &(lincount s a (&0) (&2 * B)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FAMILY_NONHOMOG_LE THEN ASM_REWRITE_TAC[] THEN
    ASM_INT_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPECL [`A:int`; `&2 * B:int`]) THEN
     ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Additive fiber counts and the Cauchy-Schwarz differencing step            *)
(* ------------------------------------------------------------------------- *)

let amcount = new_definition
 `amcount (V:num->int->int) t M a =
  CARD {z | z IN ibox t M /\ isum(1..t)(\i. V i (z i)) = a}`;;

let amreps = new_definition
 `amreps (V:num->int->int) t M =
  IMAGE (\z. isum(1..t)(\i. V i (z i))) (ibox t M)`;;

let mvf = new_definition
 `mvf t (V:num->int->int) = \i x. if i <= t then V i x else V (i - t) x`;;

let AIJOIN_HEAD = prove
 (`!t (u:num->int) (v:num->int) (V:num->int->int).
    isum(1..t)(\i. V i (ijoin t u v i)) = isum(1..t)(\i. V i (u i))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[ijoin] THEN
  COND_CASES_TAC THENL [REWRITE_TAC[]; POP_ASSUM MP_TAC THEN
   REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC]);;

let AIJOIN_TAIL = prove
 (`!t (u:num->int) (v:num->int) (V:num->int->int).
    isum((t+1)..(2*t))(\i. V (i-t) (ijoin t u v i)) = isum(1..t)(\i. V i (v
     i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`t:num`;
    `\i. (V:num->int->int) (i-t) (ijoin t (u:num->int) (v:num->int) i)`; `1`;
      `t:num`] ISUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + t = t + 1`; ARITH_RULE `t + t = 2 * t`] THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[ijoin; IN_NUMSEG] THEN
  SUBGOAL_THEN `(i+t)-t = i` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL [AP_TERM_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let MVF_HEAD = prove
 (`!t (u:num->int) (v:num->int) (V:num->int->int).
    isum(1..t)(\i. mvf t V i (ijoin t u v i)) = isum(1..t)(\i. V i (u i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`t:num`;`u:num->int`;`v:num->int`;`V:num->int->int`]
   AIJOIN_HEAD) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; mvf] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL [REWRITE_TAC[]; ASM_ARITH_TAC]);;

let MVF_TAIL = prove
 (`!t (u:num->int) (v:num->int) (V:num->int->int).
    isum((t+1)..(2*t))(\i. mvf t V i (ijoin t u v i)) = isum(1..t)(\i. V i (v
     i))`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`t:num`;`u:num->int`;`v:num->int`;`V:num->int->int`]
   AIJOIN_TAIL) THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; mvf] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]]);;

let AMREPS_FINITE = prove
 (`!(V:num->int->int) t M. FINITE(amreps V t M)`,
  REWRITE_TAC[amreps] THEN SIMP_TAC[FINITE_IMAGE; IBOX_FINITE]);;

let AMCOUNT_VANISH = prove
 (`!(V:num->int->int) t M a. ~(a IN amreps V t M) ==> amcount V t M a = 0`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[amcount] THEN
  SUBGOAL_THEN `{z | z IN ibox t M /\
   isum(1..t)(\i. V i (z i)) = a} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:num->int` THEN
    STRIP_TAC THEN UNDISCH_TAC `~(a IN amreps V t M)` THEN
     REWRITE_TAC[amreps; IN_IMAGE] THEN
    EXISTS_TAC `z:num->int` THEN ASM_MESON_TAC[];
    REWRITE_TAC[CARD_CLAUSES]]);;

let AFIBER_CARD = prove
 (`!(V:num->int->int) t M a b.
    1 <= t
    ==> CARD {w | w IN ibox (2*t) M /\
                  isum(1..t)(\i. mvf t V i (w i)) = a /\
                  isum((t+1)..(2*t))(\i. mvf t V i (w i)) = b} =
        amcount V t M a * amcount V t M b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{w | w IN ibox (2*t) M /\ isum(1..t)(\i. mvf t V i (w i)) =
    a /\ isum((t+1)..(2*t))(\i. mvf t V i (w i)) = b} =
    IMAGE (\p. ijoin t (FST p) (SND p))
          (({u | u IN ibox t M /\ isum(1..t)(\i. V i (u i)) = a}) CROSS
           ({v | v IN ibox t M /\ isum(1..t)(\i. V i (v i)) = b}))`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM;
     IN_CROSS] THEN
    X_GEN_TAC `w:num->int` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`ihead t (w:num->int)`;
        `itail t (w:num->int)`] THEN
      SUBGOAL_THEN `ijoin t (ihead t (w:num->int)) (itail t w) = w`
       ASSUME_TAC THENL
       [ASM_MESON_TAC[IJOIN_HEADTAIL]; ALL_TAC] THEN
      ASM_SIMP_TAC[IHEAD_IN; ITAIL_IN] THEN
      MP_TAC(ISPECL [`t:num`;`ihead t (w:num->int)`;`itail t
       (w:num->int)`;`V:num->int->int`] MVF_HEAD) THEN
      MP_TAC(ISPECL [`t:num`;`ihead t (w:num->int)`;`itail t
       (w:num->int)`;`V:num->int->int`] MVF_TAIL) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC IJOIN_IN THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[MVF_HEAD]; ASM_MESON_TAC[MVF_TAIL]]];
    ALL_TAC] THEN
  REWRITE_TAC[amcount] THEN
  SUBGOAL_THEN `FINITE ({u | u IN ibox t M /\
   isum(1..t)(\i. V i (u i)) = a}) /\ FINITE ({v | v IN ibox t M /\
    isum(1..t)(\i. V i (v i)) = b})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox t M` THEN
    REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. ijoin t (FST p) (SND p:num->int)`;
    `({u | u IN ibox t M /\ isum(1..t)(\i. V i (u i)) =
     a} CROSS {v | v IN ibox t M /\
      isum(1..t)(\i. V i (v i)) = b})`] CARD_IMAGE_INJ) THEN
  ASM_SIMP_TAC[FINITE_CROSS] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`u1:num->int`;`v1:num->int`;`u2:num->int`;`v2:num->int`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC IJOIN_INJ THEN MAP_EVERY EXISTS_TAC [`t:num`; `M:int`] THEN
     ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CARD_CROSS]]);;

let ADIAG_COUNT = prove
 (`!(V:num->int->int) t M.
    1 <= t
    ==> CARD {w | w IN ibox (2*t) M /\
                  isum(1..t)(\i. mvf t V i (w i)) = isum((t+1)..(2*t))(\i. mvf
                   t V i (w i))} =
        nsum (amreps V t M) (\a. amcount V t M a * amcount V t M a)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {w | w IN ibox (2*t) M /\
   isum(1..t)(\i. mvf t V i (w i)) = isum((t+1)..(2*t))(\i. mvf t V i (w
    i))}` THEN
  SUBGOAL_THEN `FINITE (S:(num->int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `ibox (2*t) M` THEN REWRITE_TAC[IBOX_FINITE] THEN
     SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM] THEN
  MP_TAC(ISPECL [`\w:num->int. isum(1..t)(\i. mvf t V i (w i))`;
    `\w:num->int. 1`; `S:(num->int)->bool`] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!y. {x | x IN S /\
   isum(1..t)(\i. mvf t V i (x i)) = y} = {w | w IN ibox (2*t) M /\
    isum(1..t)(\i. mvf t V i (w i)) = y /\
     isum((t+1)..(2*t))(\i. mvf t V i (w i)) = y}` ASSUME_TAC THENL
   [X_GEN_TAC `y:int` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:num->int` THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. nsum {w | w IN ibox (2*t) M /\
   isum(1..t)(\i. mvf t V i (w i)) = y /\
    isum((t+1)..(2*t))(\i. mvf t V i (w i)) = y} (\w:num->int. 1) = amcount V t
     M y * amcount V t M y` (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `y:int` THEN
    SUBGOAL_THEN `FINITE {w | w IN ibox (2*t) M /\
     isum(1..t)(\i. mvf t V i (w i)) = y /\
      isum((t+1)..(2*t))(\i. mvf t V i (w i)) = y}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox (2*t) M` THEN
      REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_NSUM] THEN
    MP_TAC(ISPECL [`V:num->int->int`;`t:num`;`M:int`;`y:int`;`y:int`]
     AFIBER_CARD) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN CONJ_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:int` THEN
     DISCH_THEN(X_CHOOSE_THEN `w:num->int` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[amreps; IN_IMAGE] THEN EXISTS_TAC `ihead t (w:num->int)` THEN
       CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:num`;`ihead t (w:num->int)`;`itail t
       (w:num->int)`;`V:num->int->int`] MVF_HEAD) THEN
        MP_TAC(ISPECL [`t:num`;`M:int`;`w:num->int`] IJOIN_HEADTAIL) THEN
         ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
          ASM_MESON_TAC[];
      ASM_SIMP_TAC[IHEAD_IN]];
    X_GEN_TAC `a:int` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`V:num->int->int`;`t:num`;`M:int`;`a:int`;`a:int`]
     AFIBER_CARD) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `{w | w IN ibox (2*t) M /\
     isum(1..t)(\i. mvf t V i (w i)) = a /\
      isum((t+1)..(2*t))(\i. mvf t V i (w i)) = a} = {}` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:int`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
       REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
        X_GEN_TAC `w:num->int` THEN STRIP_TAC THEN
         UNDISCH_TAC `~(a IN IMAGE (\w. isum (1..t) (\i. mvf t V i (w i))) S)`
          THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:num->int` THEN
           ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[CARD_CLAUSES]]]);;

let wtail = new_definition `wtail t (W:num->int->int) = \i x. W (i+t) x`;;

let HEAD_ISUM_W = prove
 (`!t (w:num->int) (W:num->int->int). isum(1..t)(\i. W i (ihead t w i)) =
  isum(1..t)(\i. W i (w i))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; ihead; IN_NUMSEG] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL [REWRITE_TAC[]; ASM_ARITH_TAC]);;

let TAIL_ISUM_W = prove
 (`!t (w:num->int) (W:num->int->int). isum((t+1)..(2*t))(\i. W i (w i)) =
  isum(1..t)(\i. W (i+t) (itail t w i))`,
  REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`t:num`; `\i. (W:num->int->int) i ((w:num->int) i)`; `1`;
     `t:num`] ISUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + t = t + 1`; ARITH_RULE `t + t = 2 * t`] THEN
   DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; itail; IN_NUMSEG] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL [REWRITE_TAC[]; ASM_ARITH_TAC]);;

let HEAD_ISUM_IJOIN = prove
 (`!t (u:num->int) (v:num->int) (W:num->int->int). isum(1..t)(\i. W i (ijoin t
  u v i)) = isum(1..t)(\i. W i (u i))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; ijoin; IN_NUMSEG] THEN STRIP_TAC THEN
   COND_CASES_TAC THENL [REWRITE_TAC[]; ASM_ARITH_TAC]);;

let TAIL_ISUM_IJOIN = prove
 (`!t (u:num->int) (v:num->int) (W:num->int->int). isum((t+1)..(2*t))(\i. W i
  (ijoin t u v i)) = isum(1..t)(\i. W (i+t) (v i))`,
  REPEAT GEN_TAC THEN
   MP_TAC(ISPECL [`t:num`;
     `\i. (W:num->int->int) i (ijoin t (u:num->int) (v:num->int) i)`; `1`;
       `t:num`] ISUM_OFFSET) THEN
  REWRITE_TAC[ARITH_RULE `1 + t = t + 1`; ARITH_RULE `t + t = 2 * t`] THEN
   DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; ijoin; IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(1 <= i+t /\ i+t <= t) /\ (t+1 <= i+t /\ i+t <= 2*t) /\
   (i+t)-t = i` STRIP_ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[]);;

let AFIBER_CARD_GEN = prove
 (`!(W:num->int->int) t M a b. 1 <= t
    ==> CARD {w | w IN ibox (2*t) M /\ isum(1..t)(\i. W i (w i)) = a /\
     isum((t+1)..(2*t))(\i. W i (w i)) = b} =
        amcount W t M a * amcount (wtail t W) t M b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{w:num->int | w IN ibox (2*t) M /\
    isum(1..t)(\i. (W:num->int->int) i (w i)) = a /\
     isum((t+1)..(2*t))(\i. W i (w i)) = b} =
    IMAGE (\p. ijoin t (FST p) (SND p))
          (({u:num->int | u IN ibox t M /\
           isum(1..t)(\i. W i (u i)) = a}) CROSS
           ({v:num->int | v IN ibox t M /\
            isum(1..t)(\i. W (i+t) (v i)) = b}))`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; EXISTS_PAIR_THM;
     IN_CROSS] THEN
    X_GEN_TAC `w:num->int` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`ihead t (w:num->int)`;
        `itail t (w:num->int)`] THEN
      SUBGOAL_THEN `ijoin t (ihead t (w:num->int)) (itail t w) = w`
       ASSUME_TAC THENL
       [ASM_MESON_TAC[IJOIN_HEADTAIL]; ALL_TAC] THEN
      ASM_SIMP_TAC[IHEAD_IN; ITAIL_IN; HEAD_ISUM_W] THEN
       ASM_MESON_TAC[TAIL_ISUM_W];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC IJOIN_IN THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[HEAD_ISUM_IJOIN]; ASM_MESON_TAC[TAIL_ISUM_IJOIN]]];
    ALL_TAC] THEN
  REWRITE_TAC[amcount; wtail] THEN
  SUBGOAL_THEN `FINITE ({u:num->int | u IN ibox t M /\
   isum(1..t)(\i. (W:num->int->int) i (u i)) = a}) /\
    FINITE ({v:num->int | v IN ibox t M /\
     isum(1..t)(\i. (W:num->int->int) (i+t) (v i)) = b})`
      STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox t M` THEN
    REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\p. ijoin t (FST p) (SND p:num->int)`;
    `({u:num->int | u IN ibox t M /\
     isum(1..t)(\i. (W:num->int->int) i (u i)) = a} CROSS {v:num->int | v IN
      ibox t M /\
       isum(1..t)(\i. (W:num->int->int) (i+t) (v i)) = b})`] CARD_IMAGE_INJ)
        THEN
  ASM_SIMP_TAC[FINITE_CROSS] THEN ANTS_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; IN_CROSS; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC
     [`u1:num->int`;`v1:num->int`;`u2:num->int`;`v2:num->int`] THEN
    REWRITE_TAC[PAIR_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC IJOIN_INJ THEN MAP_EVERY EXISTS_TAC [`t:num`; `M:int`] THEN
     ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[CARD_CROSS]]);;

let ACONV_COUNT_GEN = prove
 (`!(W:num->int->int) t M m. 1 <= t
    ==> CARD {w | w IN ibox (2*t) M /\ isum(1..2*t)(\i. W i (w i)) = m} =
        nsum (amreps W t M) (\a. amcount W t M a * amcount
         (wtail t W) t M (m - a))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S = {w | w IN ibox (2*t) M /\
   isum(1..2*t)(\i. (W:num->int->int) i (w i)) = m}` THEN
  SUBGOAL_THEN `FINITE (S:(num->int)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `ibox (2*t) M` THEN REWRITE_TAC[IBOX_FINITE] THEN
     SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM] THEN
  MP_TAC(ISPECL [`\w:num->int. isum(1..t)(\i. (W:num->int->int) i (w i))`;
    `\w:num->int. 1`; `S:(num->int)->bool`] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `!y. {x | x IN S /\
   isum(1..t)(\i. (W:num->int->int) i (x i)) = y} = {w | w IN ibox (2*t) M /\
    isum(1..t)(\i. W i (w i)) = y /\
     isum((t+1)..(2*t))(\i. W i (w i)) = (m - y)}` ASSUME_TAC THENL
   [X_GEN_TAC `y:int` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:num->int` THEN
     EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    (SUBGOAL_THEN `isum(1..2*t)(\i. (W:num->int->int) i (w i)) = isum(1..t)(\i.
     W i (w i)) + isum((t+1)..(2*t))(\i. W i (w i))` ASSUME_TAC THENL
      [SUBST1_TAC(ARITH_RULE `2 * t = t + t`) THEN
       SIMP_TAC[ISUM_ADD_SPLIT; ARITH_RULE `1 <= t + 1`] THEN
        REWRITE_TAC[ARITH_RULE `t + t = 2 * t`]; ALL_TAC]) THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. nsum {w | w IN ibox (2*t) M /\
   isum(1..t)(\i. (W:num->int->int) i (w i)) = y /\
    isum((t+1)..(2*t))(\i. W i (w i)) = (m - y)} (\w:num->int. 1) = amcount
     W t M y * amcount (wtail t W) t M (m - y)` (fun th ->
      REWRITE_TAC[th]) THENL
   [X_GEN_TAC `y:int` THEN
    SUBGOAL_THEN `FINITE {w | w IN ibox (2*t) M /\
     isum(1..t)(\i. (W:num->int->int) i (w i)) = y /\
      isum((t+1)..(2*t))(\i. W i (w i)) = (m - y)}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox (2*t) M` THEN
      REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_NSUM] THEN
     ASM_SIMP_TAC[AFIBER_CARD_GEN]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN CONJ_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:int` THEN
     DISCH_THEN(X_CHOOSE_THEN `w:num->int` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[amreps; IN_IMAGE] THEN
       EXISTS_TAC `ihead t (w:num->int)` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:num`;`w:num->int`;`W:num->int->int`] HEAD_ISUM_W) THEN
       MP_TAC(ISPECL [`t:num`;`M:int`;`w:num->int`] IJOIN_HEADTAIL) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[];
      ASM_SIMP_TAC[IHEAD_IN]];
    X_GEN_TAC `a:int` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`W:num->int->int`;`t:num`;`M:int`;`a:int`;`m - a:int`]
     AFIBER_CARD_GEN) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `{w | w IN ibox (2*t) M /\
     isum(1..t)(\i. (W:num->int->int) i (w i)) = a /\
      isum((t+1)..(2*t))(\i. W i (w i)) = (m - a)} = {}` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `a:int`) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
       REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
        X_GEN_TAC `w:num->int` THEN STRIP_TAC THEN
         UNDISCH_TAC `~(a IN IMAGE (\w. isum (1..t) (\i. (W:num->int->int) i (w
          i))) S)` THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:num->int` THEN
           ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[CARD_CLAUSES]]]);;

let AGEN_FOLD = prove
 (`!(W:num->int->int) t M m. 1 <= t
    ==> 2 * CARD {w | w IN ibox (2*t) M /\ isum(1..2*t)(\i. W i (w i)) = m} <=
        CARD {w | w IN ibox (2*t) M /\
         isum(1..t)(\i. mvf t W i (w i)) = isum((t+1)..(2*t))(\i. mvf t
          W i (w i))} +
        CARD {w | w IN ibox (2*t) M /\
         isum(1..t)(\i. mvf t (wtail t W) i (w i)) = isum((t+1)..(2*t))(\i. mvf
          t (wtail t W) i (w i))}`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[ACONV_COUNT_GEN; ADIAG_COUNT] THEN
  ABBREV_TAC `s = amreps W t M UNION amreps (wtail t W) t M UNION IMAGE
   (\a:int. m - a) (amreps W t M) UNION IMAGE (\a:int. m - a) (amreps
    (wtail t W) t M)` THEN
  SUBGOAL_THEN `FINITE (s:int->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    SIMP_TAC[FINITE_UNION; FINITE_IMAGE; AMREPS_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `amreps W t M SUBSET (s:int->bool) /\
   amreps (wtail t W) t M SUBSET (s:int->bool)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN CONJ_TAC THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `nsum (amreps W t M) (\a. amcount W t M a *
   amcount (wtail t W) t M (m - a)) = nsum s (\a. amcount W t M a *
    amcount (wtail t W) t M (m - a))` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:int` THEN STRIP_TAC THEN
     ASM_SIMP_TAC[AMCOUNT_VANISH; MULT_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `nsum (amreps W t M) (\a. amcount W t M a *
   amcount W t M a) = nsum s (\a. amcount W t M a * amcount
    W t M a)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:int` THEN STRIP_TAC THEN
     ASM_SIMP_TAC[AMCOUNT_VANISH; MULT_CLAUSES]; ALL_TAC] THEN
  SUBGOAL_THEN `nsum (amreps (wtail t W) t M) (\a. amcount (wtail t W) t M a *
   amcount (wtail t W) t M a) = nsum s (\a. amcount (wtail t W) t M a * amcount
    (wtail t W) t M a)` SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:int` THEN STRIP_TAC THEN
     ASM_SIMP_TAC[AMCOUNT_VANISH; MULT_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC LEMMA4 THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `a:int` THEN DISCH_TAC THEN MATCH_MP_TAC AMCOUNT_VANISH THEN
    ASM SET_TAC[];
    X_GEN_TAC `a:int` THEN DISCH_TAC THEN MATCH_MP_TAC AMCOUNT_VANISH THEN
     ASM SET_TAC[];
    X_GEN_TAC `a:int` THEN EXPAND_TAC "s" THEN
     REWRITE_TAC[IN_UNION; IN_IMAGE] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
     ASM_MESON_TAC[INT_ARITH `m - (m - x) = x:int`]]);;

let INTSEG_CARD_BND = prove
 (`!M:int. &0 <= M ==> CARD {w:int | --M <= w /\
  w <= M} <= 2 * num_of_int M + 1`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[EXACT_INT_INTERVAL_CARD; INT_ARITH
   `&0 <= M ==> --M:int <= M`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD;
              GSYM INT_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH
   `&0 <= M ==> &0:int <= M - --M + &1`] THEN
  ASM_INT_ARITH_TAC);;

let CARD_IBOX_BND = prove
 (`!t M:int. &0 <= M ==> &(CARD(ibox t M)) <= (&2 * M + &1) pow t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
   EXISTS_TAC `&((2 * num_of_int M + 1) EXP t):int` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN
    SUBGOAL_THEN `ibox t M = {z:num->int | (!i. i IN 1..t ==> z i IN {w:int |
     --M <= w /\ w <= M}) /\ (!i. ~(i IN 1..t) ==> z i = &0)}` SUBST1_TAC THENL
     [REWRITE_TAC[ibox; EXTENSION; IN_ELIM_THM] THEN
      X_GEN_TAC `z:num->int` THEN
      MATCH_MP_TAC(TAUT `(a<=>a') ==> (a/\b <=> a'/\b)`) THEN
      AP_TERM_TAC THEN ABS_TAC THEN
      MESON_TAC[INT_ARITH `abs(x:int) <= M <=> --M <= x /\ x <= M`];
        ALL_TAC] THEN
    MP_TAC(INST [`&0:int`,`d:int`] (ISPECL [`1..t`;
      `{w:int | --M <= w /\ w <= M}`] CARD_FUNSPACE)) THEN
    REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{x:int | --M < x /\ x <= M} UNION {--M}` THEN CONJ_TAC THENL
       [SIMP_TAC[FINITE_UNION; FINITE_INT_SEG; FINITE_SING];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNION; IN_SING] THEN
         INT_ARITH_TAC]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CARD_NUMSEG_1] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_SIMP_TAC[INTSEG_CARD_BND];
    REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN
    SUBGOAL_THEN `&(2 * num_of_int M + 1):int = &2 * M + &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
      ASM_SIMP_TAC[INT_OF_NUM_OF_INT]; REWRITE_TAC[INT_LE_REFL]]]);;

let SUBADD_ID = prove
 (`!a b e:num. e <= a /\ a <= b ==> (b - a) + (a - e) = b - e`,
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let WEIGHTED_LINEAR_BND = prove
 (`!(s:A->bool) (a:A->int) m (Amax:int) (mult:A->int->num) (MaxMult:num).
     FINITE s /\ (!i z. mult i z <= MaxMult)
     ==> nsum {z:A->int | (!i. i IN s ==> abs(z i) <= Amax) /\
                          (!i. ~(i IN s) ==> z i = &0) /\
                          isum s (\i. a i * z i) = m}
              (\z. nproduct s (\i. mult i (z i)))
         <= MaxMult EXP (CARD s) * lincount s a m Amax`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[lincount] THEN
  SUBGOAL_THEN `FINITE {z:A->int | (!i. i IN s ==> abs(z i) <= Amax) /\
   (!i. ~(i IN s) ==> z i = &0) /\
    isum s (\i. a i * z i) = m}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{z:A->int | (!i. i IN s ==> abs(z i) <= Amax) /\
     (!i. ~(i IN s) ==> z i = &0)}` THEN
    ASM_SIMP_TAC[COEFFBOX_FINITE] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
     SIMP_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `SL = {z:A->int | (!i. i IN s ==> abs(z i) <= Amax) /\
   (!i. ~(i IN s) ==> z i = &0) /\ isum s (\i. a i * z i) = m}` THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum (SL:(A->int)->bool) (\z:A->int. MaxMult EXP
   (CARD(s:A->bool)))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:A->int` THEN
    DISCH_TAC THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM(MATCH_MP NPRODUCT_CONST (ASSUME
     `FINITE(s:A->bool)`))] THEN
    MATCH_MP_TAC NPRODUCT_LE THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN
     DISCH_TAC THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[NSUM_CONST] THEN REWRITE_TAC[MULT_AC; LE_REFL]]);;

let gtail = new_definition `gtail k (z:num->int) = (\i. if 1 <= i then z (i +
 k) else &0)`;;

let gjoin = new_definition `gjoin k (u:num->int) (v:num->int) = (\i. if i IN
 1..k then u i else v (i - k))`;;

let IHEAD_IN_LE = prove
 (`!k G M (w:num->int). k <= G /\ w IN ibox G M ==> ihead k w IN ibox k M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM; ihead; IN_NUMSEG] THEN
   STRIP_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC[INT_ABS_NUM; INT_LE_REFL] THEN
  UNDISCH_TAC `!i. 1 <= i /\ i <= G ==> abs((w:num->int) i) <= M` THEN
  DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_ARITH_TAC);;

let GTAIL_IN = prove
 (`!k G M (w:num->int). k <= G /\ w IN ibox G M ==> gtail k w IN ibox (G-k) M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM; gtail; IN_NUMSEG] THEN
   STRIP_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THENL
   [SUBGOAL_THEN `1 <= i` (fun th -> REWRITE_TAC[th]) THENL
    [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `!i. 1 <= i /\ i <= G ==> abs((w:num->int) i) <= M` THEN
    DISCH_THEN(MP_TAC o SPEC `i+k:num`) THEN ASM_ARITH_TAC;
    COND_CASES_TAC THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `!i. ~(1 <= i /\ i <= G) ==> (w:num->int) i = &0` THEN
    DISCH_THEN(MP_TAC o SPEC `i+k:num`) THEN ASM_ARITH_TAC]);;

let GJOIN_HEADTAIL = prove
 (`!k G M (w:num->int). k <= G /\
  w IN ibox G M ==> gjoin k (ihead k w) (gtail k w) = w`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  REWRITE_TAC[gjoin; ihead; gtail; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `1 <= i-k` THEN ASM_REWRITE_TAC[] THENL
   [SUBGOAL_THEN `i-k+k = i` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
     REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC]);;

let CARD_FIBERED_BND = prove
 (`!(f:A->B) s t c. FINITE s /\ FINITE t /\ IMAGE f s SUBSET t /\
     (!y. CARD {x | x IN s /\ f x = y} <= c) ==> CARD s <= CARD t * c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:A->B`;`\x:A. 1`;`s:A->bool`] NSUM_IMAGE_GEN) THEN
   ASM_REWRITE_TAC[NSUM_CONST] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
   EXISTS_TAC `nsum (IMAGE (f:A->B) s) (\y:B. c)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `nsum {x | x IN s /\
     (f:A->B) x = y} (\x. 1) = CARD {x | x IN s /\ f x = y}` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_EQ_NSUM THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:A->bool` THEN
       ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[NSUM_CONST; FINITE_IMAGE; MULT_CLAUSES] THEN
    MATCH_MP_TAC LE_MULT2 THEN REWRITE_TAC[LE_REFL] THEN
     MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]]);;

let PROJ1_INJ_2_DP = prove
 (`!(ffam:num->num->int) P m x y:num->int.
     ~(ffam 2 1 = &0) /\
     x IN ibox 2 P /\ isum(1..2)(\j. ipoly (ffam j) 1 (x j)) = m /\
     y IN ibox 2 P /\ isum(1..2)(\j. ipoly (ffam j) 1 (y j)) = m /\
     x 1 = y 1
     ==> x = y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM; ISUM_12; IPOLY1] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `(x:num->int) 2 = (y:num->int) 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `(ffam:num->num->int) 2 1 * (x:num->int) 2 = ffam 2 1 *
    (y:num->int) 2` MP_TAC THENL
     [REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> rand(concl th) = `m:int`
      && is_eq(concl th)))) THEN
      FIRST_X_ASSUM(fun th -> REWRITE_TAC[th]) THEN INT_ARITH_TAC;
      ASM_SIMP_TAC[INT_EQ_MUL_LCANCEL]]; ALL_TAC] THEN
  REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `i = 2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(i IN 1..2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(x:num->int) i = &0 /\
   (y:num->int) i = &0` (fun th -> REWRITE_TAC[th]) THEN
  ASM_SIMP_TAC[]);;

let IHEAD_SUM_V = prove
 (`!(V:num->int->int) k (w:num->int). isum(1..k)(\i. V i (ihead k w i)) =
  isum(1..k)(\i. V i (w i))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG; ihead; IN_NUMSEG] THEN STRIP_TAC THEN
   ASM_SIMP_TAC[]);;

let GTAIL_SUM_V = prove
 (`!(V:num->int->int) k G (w:num->int). k <= G
    ==> isum(1..(G-k))(\i. V (i+k) (gtail k w i)) = isum((k+1)..G)(\i. V i (w
     i))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `isum(1..(G-k))(\i. V (i+k) (gtail k w i)) = isum(1..(G-k))(\i.
   V (i+k) (w (i+k)))` SUBST1_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; gtail] THEN STRIP_TAC THEN
    SUBGOAL_THEN `1 <= i` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:num`; `\i. (V:num->int->int) i (w i)`; `1`;
    `G-k:num`] ISUM_OFFSET) THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `1+k = k+1 /\ (G-k)+k = G` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC ISUM_EQ THEN
   X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN REWRITE_TAC[]);;

let GTAIL_FIBER_CARD_V = prove
 (`!(V:num->int->int) k G M z v. 1 <= k /\ k <= G
    ==> CARD {w | (w IN ibox G M /\ isum(1..G)(\i. V i (w i)) = z) /\
     gtail k w = v}
        <= CARD {u | u IN ibox k M /\
         isum(1..k)(\i. V i (u i)) = z - isum(1..(G-k))(\i. V (i+k) (v i))}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (ihead k) {w | (w IN ibox G M /\
   isum(1..G)(\i. V i (w i)) = z) /\ gtail k w = v})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`w1:num->int`;`w2:num->int`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `gjoin k (ihead k (w1:num->int)) (gtail k w1) = gjoin k
       (ihead k (w2:num->int)) (gtail k w2)` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN ASM_MESON_TAC[GJOIN_HEADTAIL];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox G M` THEN
       REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]];
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `u:num->int` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:num->int` STRIP_ASSUME_TAC) THEN
       ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC IHEAD_IN_LE THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IHEAD_SUM_V] THEN
      SUBGOAL_THEN `isum(k+1..G)(\i. V i ((w:num->int) i)) = isum(1..(G-k))(\i.
       V (i+k) (v i))` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`V:num->int->int`;`k:num`;`G:num`;`w:num->int`]
        GTAIL_SUM_V) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
         ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`\i. (V:num->int->int) i (w i)`;`1`;`k:num`;`G:num`]
       ISUM_COMBINE_R) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `isum (1..G) (\i. V i ((w:num->int) i)) = z` THEN
       ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox k M` THEN
       REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]]]);;

let MCOUNT_SPLIT_DP = prove
 (`!(V:num->int->int) k G M z c. 1 <= k /\ k <= G /\
     (!a. CARD {u | u IN ibox k M /\ isum(1..k)(\i. V i (u i)) = a} <= c)
     ==> CARD {w | w IN ibox G M /\ isum(1..G)(\i. V i (w i)) = z}
         <= CARD (ibox (G-k) M) * c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`gtail k :(num->int)->(num->int)`;
                 `{w | w IN ibox G M /\ isum(1..G)(\i. V i (w i)) = z}`;
                 `ibox (G-k) M`; `c:num`] CARD_FIBERED_BND) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox G M` THEN
      REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[];
      REWRITE_TAC[IBOX_FINITE];
      REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN
       X_GEN_TAC `vv:num->int` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:num->int` STRIP_ASSUME_TAC) THEN
       ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC GTAIL_IN THEN ASM_MESON_TAC[];
      X_GEN_TAC `vv:num->int` THEN
      SUBGOAL_THEN `{x | x IN {w | w IN ibox G M /\
       isum(1..G)(\i. V i (w i)) = z} /\ gtail k x = vv} =
                    {w | (w IN ibox G M /\ isum(1..G)(\i. V i (w i)) = z) /\
                     gtail k w = vv}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
      MATCH_MP_TAC LE_TRANS THEN
      EXISTS_TAC `CARD {u | u IN ibox k M /\
       isum(1..k)(\i. V i (u i)) = z - isum(1..(G-k))(\i. V (i+k) (vv
        i))}` THEN
      CONJ_TAC THENL [MATCH_MP_TAC GTAIL_FIBER_CARD_V THEN
       ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    REWRITE_TAC[]]);;

let findiffset_dp = new_definition
 `findiffset_dp (ffam:num->num->int) e kk P =
    {p | p IN ibox (2*kk) (&2 * P) /\
         isum(1..kk)(\i. ipoly (ffam i) e (p i + p(i+kk)) - ipoly (ffam i) e (p
          i)) = &0}`;;

let REPARAM_COND_DP = prove
 (`!(ffam:num->num->int) e kk P (w:num->int). 1 <= kk /\ w IN ibox (2*kk) P /\
     isum(1..kk)(\i. mvf kk (\j. ipoly (ffam j) e) i (w i)) =
     isum((kk+1)..(2*kk))(\i. mvf kk (\j. ipoly (ffam j) e) i (w i))
     ==> isum(1..kk)(\i. ipoly (ffam i) e (reparam kk w i + reparam kk w
      (i+kk))
                         - ipoly (ffam i) e (reparam kk w i)) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN STRIP_TAC THEN
  SIMP_TAC[ISUM_SUB; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `!i. i IN 1..kk ==> reparam kk (w:num->int) i = w(i+kk) /\
                                   reparam kk w (i+kk) = w i - w(i+kk)`
                                    ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    REWRITE_TAC[reparam] THEN
    REWRITE_TAC[IN_NUMSEG] THEN
    SUBGOAL_THEN `(1 <= i /\ i <= kk /\ ~(1 <= i+kk /\ i+kk <= kk) /\
     (kk+1 <= i+kk /\ i+kk <= 2*kk) /\ (i+kk)-kk = i):bool` MP_TAC THENL
     [UNDISCH_TAC `1 <= i` THEN UNDISCH_TAC `i <= kk` THEN
      UNDISCH_TAC `1 <= kk` THEN ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `isum(1..kk)(\i. mvf kk (\j. ipoly (ffam j) e) i (w i)) =
   isum(1..kk)(\i. ipoly (ffam i) e (w i))` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; mvf] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL [REWRITE_TAC[]; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `isum((kk+1)..(2*kk))(\i. mvf kk (\j. ipoly (ffam j) e) i (w i))
   = isum(1..kk)(\i. ipoly (ffam i) e (w(i+kk)))` SUBST_ALL_TAC THENL
   [REWRITE_TAC[ISUM_TAILSHIFT] THEN MATCH_MP_TAC ISUM_EQ THEN
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG; mvf] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(i + kk <= kk) /\ (i+kk)-kk = i` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `isum(1..kk)(\i. ipoly (ffam i) e (reparam kk (w:num->int) i +
   reparam kk w (i+kk))) = isum(1..kk)(\i. ipoly (ffam i) e (w i)) /\
                isum(1..kk)(\i. ipoly (ffam i) e (reparam kk (w:num->int) i)) =
                 isum(1..kk)(\i. ipoly (ffam i) e (w(i+kk)))`
   (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC) THEN
  CONJ_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN AP_TERM_TAC THEN INT_ARITH_TAC);;

let IHSTEP_FINDIFF_DP = prove
 (`!(ffam:num->num->int) e kk P. 1 <= kk
    ==> CARD {w | w IN ibox (2*kk) P /\
                  isum(1..kk)(\i. mvf kk (\j. ipoly (ffam j) e) i (w i)) =
                  isum((kk+1)..(2*kk))(\i. mvf kk (\j. ipoly (ffam j) e) i (w
                   i))}
        <= CARD (findiffset_dp ffam e kk P)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (reparam kk) {w | w IN ibox (2*kk) P /\
   isum(1..kk)(\i. mvf kk (\j. ipoly ((ffam:num->num->int) j) e) i (w i)) =
    isum((kk+1)..(2*kk))(\i. mvf kk (\j. ipoly (ffam j) e) i (w i))})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`w:num->int`;`w':num->int`] THEN STRIP_TAC THEN
      MATCH_MP_TAC REPARAM_INJ THEN
       MAP_EVERY EXISTS_TAC [`kk:num`;`P:int`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox (2*kk) P` THEN
       REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM; findiffset_dp] THEN
    X_GEN_TAC `p:num->int` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:num->int` STRIP_ASSUME_TAC) THEN
     ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC REPARAM_IN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC REPARAM_COND_DP THEN MAP_EVERY EXISTS_TAC [`P:int`] THEN
       ASM_REWRITE_TAC[]];
    REWRITE_TAC[findiffset_dp] THEN MATCH_MP_TAC FINITE_SUBSET THEN
     EXISTS_TAC `ibox (2*kk) (&2 * P)` THEN REWRITE_TAC[IBOX_FINITE] THEN
      SET_TAC[]]);;

let FINDIFFSET_AS_PAIRS_DP = prove
 (`!(ffam:num->num->int) e kk P. 1 <= kk
    ==> findiffset_dp ffam e kk P =
        IMAGE (\pr. ijoin kk (FST pr) (SND pr))
          {yh | FST yh IN ibox kk (&2 * P) /\ SND yh IN ibox kk (&2 * P) /\
                isum(1..kk)(\i. ipoly (ffam i) e (FST yh i + SND yh i) - ipoly
                 (ffam i) e (FST yh i)) = &0}`,
  REPEAT STRIP_TAC THEN
   REWRITE_TAC[findiffset_dp; EXTENSION; IN_IMAGE; IN_ELIM_THM;
     EXISTS_PAIR_THM] THEN
  X_GEN_TAC `p:num->int` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`ihead kk (p:num->int)`;
      `itail kk (p:num->int)`] THEN
    SUBGOAL_THEN `ijoin kk (ihead kk (p:num->int)) (itail kk p) = p`
     ASSUME_TAC THENL
     [ASM_MESON_TAC[IJOIN_HEADTAIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[IHEAD_IN; ITAIL_IN] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `isum(1..kk)(\i. ipoly (ffam i) e ((p:num->int) i + p(i+kk)) -
     ipoly (ffam i) e (p i))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
     REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(1 <= i /\ i <= kk):bool` ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ihead; itail; IN_NUMSEG] THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC IJOIN_IN THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `isum(1..kk)(\i. ipoly (ffam i) e ((p1:num->int) i +
       (p2:num->int) i) - ipoly (ffam i) e (p1 i))` THEN
      CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
      MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
       REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(1 <= i /\ i <= kk /\ ~(1 <= i+kk /\ i+kk <= kk) /\
       (kk+1 <= i+kk /\ i+kk <= 2*kk) /\
        (i+kk)-kk=i):bool` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ijoin; IN_NUMSEG] THEN ASM_REWRITE_TAC[]]]);;

let PAIRSET_FINITE_DP = prove
 (`!(ffam:num->num->int) e kk P. FINITE {yh:(num->int)#(num->int) | FST yh IN
  ibox kk (&2 * P) /\ SND yh IN ibox kk (&2 * P) /\
                isum(1..kk)(\i. ipoly (ffam i) e (FST yh i + SND yh i) - ipoly
                 (ffam i) e (FST yh i)) = &0}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `(ibox kk (&2 * P)) CROSS (ibox kk (&2 * P))` THEN
  CONJ_TAC THENL
   [SIMP_TAC[FINITE_CROSS; IBOX_FINITE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; FORALL_PAIR_THM; IN_CROSS] THEN
     SIMP_TAC[]]);;

let CARD_FINDIFFSET_PAIRS_DP = prove
 (`!(ffam:num->num->int) e kk P. 1 <= kk
    ==> CARD(findiffset_dp ffam e kk P) =
        CARD {yh:(num->int)#(num->int) | FST yh IN ibox kk (&2 * P) /\
         SND yh IN ibox kk (&2 * P) /\
                isum(1..kk)(\i. ipoly (ffam i) e (FST yh i + SND yh i) - ipoly
                 (ffam i) e (FST yh i)) = &0}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[FINDIFFSET_AS_PAIRS_DP] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[PAIRSET_FINITE_DP] THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`u1:num->int`;`v1:num->int`;`u2:num->int`;`v2:num->int`]
   THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u1:num->int) = u2 /\ (v1:num->int) = v2` MP_TAC THENL
   [MATCH_MP_TAC IJOIN_INJ THEN
    MAP_EVERY EXISTS_TAC [`kk:num`; `&2 * P:int`] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[PAIR_EQ] THEN SIMP_TAC[]]);;

let PS_FIBER_CARD_DP = prove
 (`!(ffam:num->num->int) e kk P hh. hh IN ibox kk (&2 * P)
    ==> CARD {x:(num->int)#(num->int) |
                (FST x IN ibox kk (&2 * P) /\ SND x IN ibox kk (&2 * P) /\
                 isum(1..kk)(\i. ipoly (ffam i) e (FST x i + SND x i) - ipoly
                  (ffam i) e (FST x i)) = &0)
                /\ SND x = hh}
        = CARD {y:num->int | y IN ibox kk (&2 * P) /\
                        isum(1..kk)(\i. ipoly (ffam i) e (y i + hh i) - ipoly
                         (ffam i) e (y i)) = &0}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x:(num->int)#(num->int) |
       (FST x IN ibox kk (&2 * P) /\ SND x IN ibox kk (&2 * P) /\
        isum(1..kk)(\i. ipoly (ffam i) e (FST x i + SND x i) - ipoly (ffam i) e
         (FST x i)) = &0)
       /\ SND x = hh} =
    IMAGE (\y:num->int. (y,hh))
      {y:num->int | y IN ibox kk (&2 * P) /\
                    isum(1..kk)(\i. ipoly (ffam i) e (y i + hh i) - ipoly (ffam
                     i) e (y i)) = &0}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM; FORALL_PAIR_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:num->int`; `b:num->int`] THEN
    REWRITE_TAC[PAIR_EQ] THEN REWRITE_TAC[FST; SND] THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `a:num->int` THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `isum(1..kk)(\i. ipoly (ffam i) e ((a:num->int) i +
       (b:num->int) i) - ipoly (ffam i) e (a i)) = &0` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `isum(1..kk)(\i. ipoly (ffam i) e ((a:num->int) i +
       (hh:num->int) i) - ipoly (ffam i) e (a i)) = &0` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
   MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
    [REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN SIMP_TAC[];
     MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox kk (&2 * P)` THEN
      REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]]);;

let PAIRSET_FIBERSUM_DP = prove
 (`!(ffam:num->num->int) e kk P.
    CARD {yh:(num->int)#(num->int) | FST yh IN ibox kk (&2 * P) /\
     SND yh IN ibox kk (&2 * P) /\
                isum(1..kk)(\i. ipoly (ffam i) e (FST yh i + SND yh i) - ipoly
                 (ffam i) e (FST yh i)) = &0}
        = nsum (ibox kk (&2 * P))
            (\hh. CARD {y:num->int | y IN ibox kk (&2 * P) /\
                        isum(1..kk)(\i. ipoly (ffam i) e (y i + hh i) - ipoly
                         (ffam i) e (y i)) = &0})`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `PS = {yh:(num->int)#(num->int) | FST yh IN ibox kk (&2 * P) /\
   SND yh IN ibox kk (&2 * P) /\
                isum(1..kk)(\i. ipoly ((ffam:num->num->int) i) e (FST yh i +
                 SND yh i) - ipoly (ffam i) e (FST yh i)) = &0}` THEN
  SUBGOAL_THEN `FINITE (PS:((num->int)#(num->int))->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "PS" THEN REWRITE_TAC[PAIRSET_FINITE_DP]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM] THEN
  MP_TAC(ISPECL [`SND:(num->int)#(num->int)->(num->int)`;
    `\x:(num->int)#(num->int). 1`;
      `PS:((num->int)#(num->int))->bool`] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum (IMAGE (SND:(num->int)#(num->int)->num->int) PS)
                (\hh. CARD {y:num->int | y IN ibox kk (&2 * P) /\
                        isum(1..kk)(\i. ipoly ((ffam:num->num->int) i) e (y i +
                         hh i) - ipoly (ffam i) e (y i)) = &0})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `hh:num->int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(hh:num->int) IN ibox kk (&2 * P)` ASSUME_TAC THENL
     [UNDISCH_TAC `(hh:num->int) IN IMAGE (SND:(num->int)#(num->int)->num->int)
      PS` THEN
      REWRITE_TAC[IN_IMAGE] THEN
       DISCH_THEN(X_CHOOSE_THEN `x:(num->int)#(num->int)`
        STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:(num->int)#(num->int)) IN PS` THEN EXPAND_TAC "PS" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE {x:(num->int)#(num->int) | x IN PS /\
     SND x = hh}` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `PS:((num->int)#(num->int))->bool` THEN ASM_REWRITE_TAC[] THEN
       SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_NSUM] THEN
    MP_TAC(SPECL [`ffam:num->num->int`;`e:num`;`kk:num`;`P:int`;`hh:num->int`]
     PS_FIBER_CARD_DP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    AP_TERM_TAC THEN EXPAND_TAC "PS" THEN
     REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:(num->int)#(num->int)` THEN REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC NSUM_SUPERSET THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `hh:num->int` THEN
    DISCH_THEN(X_CHOOSE_THEN `yh:(num->int)#(num->int)` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(yh:(num->int)#(num->int)) IN PS` THEN
    EXPAND_TAC "PS" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
    X_GEN_TAC `hh:num->int` THEN STRIP_TAC THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    SUBGOAL_THEN `{y:num->int | y IN ibox kk (&2 * P) /\
                        isum(1..kk)(\i. ipoly ((ffam:num->num->int) i) e (y i +
                         hh i) - ipoly (ffam i) e (y i)) = &0} = {}`
                          SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM] THEN
      X_GEN_TAC `y:num->int` THEN STRIP_TAC THEN
      UNDISCH_TAC `~((hh:num->int) IN IMAGE
       (SND:(num->int)#(num->int)->num->int) PS)` THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(y:num->int,hh:num->int)` THEN
      REWRITE_TAC[SND] THEN EXPAND_TAC "PS" THEN
       REWRITE_TAC[IN_ELIM_THM; FST; SND] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CARD_CLAUSES]]]);;

let FINDIFFSET_FIBERSUM_DP = prove
 (`!(ffam:num->num->int) e kk P. 1 <= kk
    ==> (&(CARD(findiffset_dp ffam e kk P)):int) =
        &(nsum (ibox kk (&2 * P))
            (\hh. CARD {y:num->int | y IN ibox kk (&2 * P) /\
                        isum(1..kk)(\i. ipoly (ffam i) e (y i + hh i) - ipoly
                         (ffam i) e (y i)) = &0}))`,
  REPEAT STRIP_TAC THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CARD_FINDIFFSET_PAIRS_DP] THEN
   REWRITE_TAC[PAIRSET_FIBERSUM_DP]);;

let DIAG_HEAD_LE_FDFS = prove
 (`!(ffam:num->num->int) e kk P. 1 <= kk
   ==> CARD {w | w IN ibox (2*kk) P /\
                 isum(1..kk)(\i. mvf kk (\j. ipoly (ffam j) e) i (w i))
                  =
                 isum((kk+1)..(2*kk))(\i. mvf kk (\j. ipoly (ffam j) e)
                  i (w i))}
       <= CARD (findiffset_dp ffam e kk P)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC IHSTEP_FINDIFF_DP THEN ASM_REWRITE_TAC[]);;

let DIAG_TAIL_LE_FDFS = prove
 (`!(ffam:num->num->int) e kk P. 1 <= kk
   ==> CARD {w | w IN ibox (2*kk) P /\
                 isum(1..kk)(\i. mvf kk (wtail kk (\j. ipoly (ffam j) e)) i (w
                  i)) =
                 isum((kk+1)..(2*kk))(\i. mvf kk (wtail kk (\j. ipoly (ffam j)
                  e)) i (w i))}
       <= CARD (findiffset_dp (\n. ffam (n+kk)) e kk P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `mvf kk (wtail kk (\j. ipoly ((ffam:num->num->int) j) e)) = mvf
   kk (\j. ipoly ((\n. ffam(n+kk)) j) e)` SUBST1_TAC THENL
   [REWRITE_TAC[wtail; mvf; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC IHSTEP_FINDIFF_DP THEN ASM_REWRITE_TAC[]);;

let WNSUM_FOLD = prove
 (`!(Wf:(num->int)->num->int->int) t M HH.
     1 <= t /\ FINITE HH
     ==> 2 * nsum HH (\hh. CARD {y | y IN ibox (2*t) M /\
      isum(1..2*t)(\i. Wf hh i (y i)) = &0})
         <= nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
                 isum(1..t)(\i. mvf t (Wf hh) i (w i)) =
                  isum(t+1..2*t)(\i. mvf t (Wf hh) i (w i))})
          + nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
                 isum(1..t)(\i. mvf t (wtail t (Wf hh)) i (w i)) =
                  isum(t+1..2*t)(\i. mvf t (wtail t (Wf hh)) i (w i))})`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NSUM_LMUL] THEN
  ASM_SIMP_TAC[GSYM NSUM_ADD] THEN MATCH_MP_TAC NSUM_LE THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `hh:num->int` THEN DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MP_TAC(ISPECL [`(Wf:(num->int)->num->int->int) hh`; `t:num`; `M:int`;
    `&0:int`] AGEN_FOLD) THEN
  ASM_REWRITE_TAC[]);;

let MVF_HEAD_DIAG = prove
 (`!(W:num->int->int) t (w:num->int).
     isum(1..t)(\i. mvf t W i (w i)) = isum(1..t)(\i. W i (w i)) /\
     isum(t+1..2*t)(\i. mvf t W i (w i)) = isum(1..t)(\i. W i
      (w(i+t)))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; mvf] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MP_TAC(ISPECL [`t:num`; `\i. mvf t (W:num->int->int) i (w i)`; `1`;
      `t:num`] ISUM_OFFSET) THEN
    REWRITE_TAC[ARITH_RULE `1 + t = t + 1`; ARITH_RULE `t + t = 2 * t`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; mvf] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ARITH_RULE `(i+t)-t = i`]]]);;

let MVF_TAIL_DIAG = prove
 (`!(W:num->int->int) t (w:num->int).
     isum(1..t)(\i. mvf t (wtail t W) i (w i)) = isum(1..t)(\i. W (i+t) (w i))
      /\
     isum(t+1..2*t)(\i. mvf t (wtail t W) i (w i)) = isum(1..t)(\i. W (i+t)
      (w(i+t)))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; mvf; wtail] THEN
    STRIP_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    MP_TAC(ISPECL [`t:num`; `\i. mvf t (wtail t (W:num->int->int)) i (w i)`;
      `1`; `t:num`] ISUM_OFFSET) THEN
    REWRITE_TAC[ARITH_RULE `1 + t = t + 1`; ARITH_RULE `t + t = 2 * t`] THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG; mvf; wtail] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[ARITH_RULE `(i+t)-t = i`]]]);;

let NEG_IPOLY = prove
 (`!(psi:num->int) d y:int. ipoly (\i. --(psi i)) d y = --(ipoly psi d y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ipoly] THEN
  REWRITE_TAC[GSYM ISUM_NEG] THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN DISCH_TAC THEN
   INT_ARITH_TAC);;

let sgnf = new_definition
 `sgnf (phi:num->num->int) (neg:num->bool) j =
  if neg j then (\i. --(phi j i)) else phi j`;;

let SGNF_IPOLY = prove
 (`!(phi:num->num->int) neg j d y:int.
     ipoly (sgnf phi neg j) d y = (if neg j then --(ipoly (phi j) d y) else
      ipoly (phi j) d y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sgnf] THEN COND_CASES_TAC THEN
  REWRITE_TAC[NEG_IPOLY] THEN REWRITE_TAC[ETA_AX]);;

let SGNF_LEAD = prove
 (`!(phi:num->num->int) neg j d. ~(phi j d = &0) ==> ~(sgnf phi neg j d = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sgnf] THEN COND_CASES_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN INT_ARITH_TAC);;

let SGNF_ABS = prove
 (`!(phi:num->num->int) neg j i. abs(sgnf phi neg j i) = abs(phi j i)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sgnf] THEN COND_CASES_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN INT_ARITH_TAC);;

let ISUM_CONST_LINCOUNT = prove
 (`!(s:num->bool) (MaxMult:num) A B (mfn:(num->int)->int).
     isum {a:num->int | (!i. i IN s ==> abs(a i) <= A) /\
      (!i. ~(i IN s) ==> a i = &0)}
          (\a. &(MaxMult EXP (CARD s)) * &(lincount s a (mfn a) B))
     = &(MaxMult EXP (CARD s)) *
       isum {a:num->int | (!i. i IN s ==> abs(a i) <= A) /\
        (!i. ~(i IN s) ==> a i = &0)}
            (\a. &(lincount s a (mfn a) B))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ISUM_LMUL]);;

let TAIL_SPLIT = prove
 (`!(V:num->int->int) t (w:num->int).
     isum(t+1..2*t)(\i. (if i <= t then V i (w i) else --(V (i-t) (w i)))) =
      --(isum(1..t)(\i. V i (w(i+t))))`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `t+1 = 1+t /\ 2*t = t+t` STRIP_ASSUME_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[ISUM_OFFSET] THEN
  REWRITE_TAC[GSYM ISUM_NEG] THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(i+t <= t) /\ (i+t)-t = i` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]);;

let HEAD_SPLIT = prove
 (`!(V:num->int->int) t (w:num->int).
     isum(1..t)(\i. (if i <= t then V i (w i) else --(V (i-t) (w i)))) =
      isum(1..t)(\i. V i (w i))`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC ISUM_EQ THEN
  X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `i <= t` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let DIAG_SIGNED_EQ = prove
 (`!(V:num->int->int) t M.
     CARD {w | w IN ibox (2*t) M /\
      isum(1..t)(\i. V i (w i)) = isum(1..t)(\i. V i (w(i+t)))}
   = CARD {w | w IN ibox (2*t) M /\
               isum(1..2*t)(\i. (if i <= t then V i (w i) else --(V (i-t) (w
                i)))) = &0}`,
  REPEAT GEN_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `w:num->int` THEN
   MATCH_MP_TAC(TAUT `(b<=>c) ==> (a/\b<=>a/\c)`) THEN
  SUBGOAL_THEN
   `isum(1..2*t)(\i. (if i <= t then (V:num->int->int) i (w i) else --(V (i-t)
    (w i))))
    = isum(1..t)(\i. V i (w i)) + --(isum(1..t)(\i. V i (w(i+t))))`
     SUBST1_TAC THENL
   [SUBST1_TAC(ARITH_RULE `2*t = t+t`) THEN
    SIMP_TAC[ISUM_ADD_SPLIT; ARITH_RULE `1 <= t+1`] THEN
    REWRITE_TAC[ARITH_RULE `t+t = 2*t`] THEN
    SUBGOAL_THEN `isum(1..t)(\i. (if i <= t then (V:num->int->int) i (w i) else
     --(V (i-t) (w i)))) = isum(1..t)(\i. V i (w i))` SUBST1_TAC THENL
     [REWRITE_TAC[HEAD_SPLIT]; ALL_TAC] THEN
    REWRITE_TAC[TAIL_SPLIT];
    INT_ARITH_TAC]);;

let DIAG_SIGNFAM = prove
 (`!(V:num->int->int) t M.
     CARD {w | w IN ibox (2*t) M /\
      isum(1..t)(\i. V i (w i)) = isum(1..t)(\i. V i (w(i+t)))}
   = CARD {w | w IN ibox (2*t) M /\
    isum(1..2*t)(\i. signfam V t i (w i)) = &0}`,
  REWRITE_TAC[SIGNED_FAM] THEN REWRITE_TAC[DIAG_SIGNED_EQ]);;

let HEADSUM_SIGNFAM = prove
 (`!(Wf:(num->int)->num->int->int) t M HH.
     nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
             isum(1..t)(\i. mvf t (Wf hh) i (w i)) = isum(t+1..2*t)(\i.
              mvf t (Wf hh) i (w i))})
       = nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
        isum(1..2*t)(\i. signfam (Wf hh) t i (w i)) = &0})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `hh:num->int` THEN
   DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[MVF_HEAD_DIAG] THEN REWRITE_TAC[GSYM DIAG_SIGNFAM]);;

let TAILSUM_SIGNFAM = prove
 (`!(Wf:(num->int)->num->int->int) t M HH.
     nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
             isum(1..t)(\i. mvf t (wtail t (Wf hh)) i (w i)) =
              isum(t+1..2*t)(\i. mvf t (wtail t (Wf hh)) i (w i))})
       = nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
        isum(1..2*t)(\i. signfam (\j. Wf hh (j+t)) t i (w i)) = &0})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `hh:num->int` THEN
   DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  REWRITE_TAC[MVF_TAIL_DIAG] THEN
  MP_TAC(ISPECL [`\j. (Wf:(num->int)->num->int->int) hh (j+t)`; `t:num`;
    `M:int`] DIAG_SIGNFAM) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
   REWRITE_TAC[]);;

let FOLD_TO_SIGNFAM = prove
 (`!(Wf:(num->int)->num->int->int) t M HH.
     1 <= t /\ FINITE HH
     ==> 2 * nsum HH (\hh. CARD {y | y IN ibox (2*t) M /\
      isum(1..2*t)(\i. Wf hh i (y i)) = &0})
         <= nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
          isum(1..2*t)(\i. signfam (Wf hh) t i (w i)) = &0})
          + nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
           isum(1..2*t)(\i. signfam (\j. Wf hh (j+t)) t i (w i)) = &0})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`Wf:(num->int)->num->int->int`;`t:num`;`M:int`;`HH:(num->int)->bool`]
    WNSUM_FOLD) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM HEADSUM_SIGNFAM; GSYM TAILSUM_SIGNFAM]);;

let TOWER_ARITH = prove
 (`!p FS SH ST B:num. 2*FS <= SH+ST /\ p*SH <= p*B /\
  p*ST <= p*B ==> (2*p)*FS <= (2*p)*B`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `p*(SH+ST):num` THEN CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `(2*p)*FS = p*(2*FS)`] THEN
    ASM_SIMP_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LEFT_ADD_DISTRIB; ARITH_RULE `(2*p)*B = p*B + p*B`] THEN
    MATCH_MP_TAC LE_ADD2 THEN ASM_REWRITE_TAC[]]);;

let IBOX_PULL = prove
 (`!(p:num->num) n M (w:num->int).
     p permutes 1..n /\ w IN ibox n M ==> (\i. w(p i)) IN ibox n M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ibox; IN_ELIM_THM] THEN BETA_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[ibox; IN_ELIM_THM]) THEN STRIP_TAC THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(fun th ->
     if (try free_in `(abs:int->int)` (concl th) with _ -> false)
    then MATCH_MP_TAC th else NO_TAC) THEN
    MP_TAC(ISPECL [`p:num->num`;`n:num`;`i:num`] PERMUTES_IN_NUMSEG) THEN
     ASM_REWRITE_TAC[IN_NUMSEG];
    SUBGOAL_THEN `(p:num->num) i = i` (fun th -> REWRITE_TAC[th]) THENL
     [UNDISCH_TAC `p permutes 1..n` THEN REWRITE_TAC[permutes] THEN
      DISCH_THEN(MP_TAC o SPEC `i:num` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let IBOX_PULL_INJ = prove
 (`!(p:num->num) n M (w1:num->int) (w2:num->int).
     p permutes 1..n /\ w1 IN ibox n M /\ w2 IN ibox n M /\
     (\i. w1(p i)) = (\i. w2(p i)) ==> w1 = w2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
  FIRST_X_ASSUM(MP_TAC o C AP_THM `inverse (p:num->num) j`) THEN BETA_TAC THEN
  MP_TAC(ISPECL [`p:num->num`;`1..n`] PERMUTES_INVERSES) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]));;

let ISUM_PERMUTE = prove
 (`!(p:num->num) n (g:num->int). p permutes 1..n
     ==> isum(1..n)(\i. g(p i)) = isum(1..n) g`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC ISUM_EQ_GENERAL_INVERSES THEN
  MAP_EVERY EXISTS_TAC [`p:num->num`; `inverse(p:num->num)`] THEN
  CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN BETA_TAC THENL
   [MP_TAC(ISPECL [`inverse(p:num->num)`;`n:num`;`i:num`] PERMUTES_IN_NUMSEG)
    THEN
    ASM_SIMP_TAC[PERMUTES_INVERSE; IN_NUMSEG] THEN
    MP_TAC(ISPECL [`p:num->num`;`1..n`] PERMUTES_INVERSES) THEN
     ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]);
    MP_TAC(ISPECL [`p:num->num`;`n:num`;`i:num`] PERMUTES_IN_NUMSEG) THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN
    MP_TAC(ISPECL [`p:num->num`;`1..n`] PERMUTES_INVERSES) THEN
     ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT2 th])]);;

let FIBER_IMGSET = prove
 (`!(p:num->num) n M (V:num->int->int). p permutes 1..n ==>
     {w | w IN ibox n M /\ isum(1..n)(\i. (V:num->int->int) (p i) (w i)) = &0}
       = IMAGE (\w. (\i. w(p i))) {w | w IN ibox n M /\
        isum(1..n)(\j. V j (w j)) = &0}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP PERMUTES_INVERSES) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
   X_GEN_TAC `w:num->int` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    EXISTS_TAC `\j:num. (w:num->int)(inverse (p:num->num) j)` THEN
     REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `x:num` THEN BETA_TAC THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`inverse(p:num->num)`;`n:num`;`M:int`;`w:num->int`]
       IBOX_PULL) THEN ASM_SIMP_TAC[PERMUTES_INVERSE];
      MP_TAC(ISPECL [`p:num->num`;`n:num`;`\j:num. (V:num->int->int) j
       ((w:num->int)(inverse (p:num->num) j))`] ISUM_PERMUTE) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if (try lhs(concl th)=`w:num->int` with _->false)
     then SUBST1_TAC th else NO_TAC) THEN
    BETA_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`p:num->num`;`n:num`;`M:int`;`x':num->int`] IBOX_PULL)
      THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`p:num->num`;`n:num`;`\i:num. (V:num->int->int) i
       ((x':num->int) i)`] ISUM_PERMUTE) THEN
      ASM_REWRITE_TAC[] THEN BETA_TAC THEN DISCH_THEN SUBST1_TAC THEN
       ASM_REWRITE_TAC[]]]);;

let FIBER_PERMUTE = prove
 (`!(p:num->num) n M (V:num->int->int).
     p permutes 1..n
     ==> CARD {w | w IN ibox n M /\ isum(1..n)(\i. V i (w i)) = &0}
       = CARD {w | w IN ibox n M /\ isum(1..n)(\i. V (p i) (w i)) = &0}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP FIBER_IMGSET th]) THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC IBOX_PULL_INJ THEN
     MAP_EVERY EXISTS_TAC [`p:num->num`;`n:num`;`M:int`] THEN
      ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox n M` THEN
     REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]]);;

let NSUM_FIBER_PERMUTE = prove
 (`!(p:num->num) t M (Wf:(num->int)->num->int->int) (HH:(num->int)->bool).
     p permutes 1..(2*t)
     ==> nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
      isum(1..2*t)(\i. Wf hh i (w i)) = &0})
       = nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
        isum(1..2*t)(\i. Wf hh (p i) (w i)) = &0})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `hh:num->int` THEN
   DISCH_TAC THEN
  MP_TAC(ISPECL [`p:num->num`; `2*t`; `M:int`;
    `(Wf:(num->int)->num->int->int) hh`] FIBER_PERMUTE) THEN
  ASM_REWRITE_TAC[]);;

let GEN_FOLD = prove
 (`!(p:num->num) t M (Wf:(num->int)->num->int->int) (HH:(num->int)->bool).
     1 <= t /\ FINITE HH /\ p permutes 1..(2*t)
     ==> 2 * nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
      isum(1..2*t)(\i. Wf hh i (w i)) = &0})
         <= nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
          isum(1..2*t)(\i. signfam (\k. Wf hh (p k)) t i (w i)) = &0})
          + nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
           isum(1..2*t)(\i. signfam (\j. Wf hh (p(j+t))) t i (w i)) = &0})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`p:num->num`; `t:num`; `M:int`;
    `Wf:(num->int)->num->int->int`;
      `HH:(num->int)->bool`] NSUM_FIBER_PERMUTE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`\hh k. (Wf:(num->int)->num->int->int) hh ((p:num->num) k)`;
    `t:num`; `M:int`; `HH:(num->int)->bool`] FOLD_TO_SIGNFAM) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV));;

let PLEAF_AGREES = prove
 (`!s (Wf:(num->int)->num->int->int) t pp pp' bp bp'.
     (!j. j < s ==> pp j = pp' j) /\ (!j. j < s ==> (bp j <=> bp' j))
     ==> pleaf s Wf t pp bp = pleaf s Wf t pp' bp'`,
  INDUCT_TAC THEN REWRITE_TAC[PLEAF] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(pp:num->num->num) 0 = pp' 0 /\
   ((bp:num->bool) 0 <=> bp' 0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then MATCH_MP_TAC ih else
   NO_TAC) THEN
  CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

let PLEAF_CONS = prove
 (`!s (Wf:(num->int)->num->int->int) t pp b bp.
     pleaf (SUC s) Wf t pp (\n. if n = 0 then b else bp(n-1))
   = pleaf s (childfam Wf t (pp 0) b) t (\j. pp(j+1)) bp`,
  REPEAT GEN_TAC THEN REWRITE_TAC[PLEAF] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC PLEAF_AGREES THEN
  CONJ_TAC THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN BETA_TAC THEN
  REWRITE_TAC[ADD_EQ_0; ARITH_RULE `~(j+1=0)`; ARITH_RULE `(j+1)-1=j`]);;

let PGEN_TOWER = prove
 (`!t M HH. 1 <= t /\ FINITE HH ==>
   !s (Wf:(num->int)->num->int->int) (pp:num->num->num) B.
     (!j. (pp j) permutes 1..(2*t))
     /\ (!bp:num->bool. nsum HH (\hh. CARD {y | y IN ibox (2*t) M /\
      isum(1..2*t)(\i. pleaf s Wf t pp bp hh i (y i)) = &0}) <= B)
     ==> 2 EXP s * nsum HH (\hh. CARD {y | y IN ibox (2*t) M /\
      isum(1..2*t)(\i. Wf hh i (y i)) = &0}) <= 2 EXP s * B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[PLEAF; EXP; MULT_CLAUSES] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `(\n. F):num->bool`) THEN
     REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`Wf:(num->int)->num->int->int`; `pp:num->num->num`;
    `B:num`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!b. 2 EXP s * nsum HH (\hh. CARD {y | y IN ibox (2*t) M /\
        isum(1..2*t)(\i. childfam (Wf:(num->int)->num->int->int) t (pp 0) b hh
         i (y i)) = &0}) <= 2 EXP s * B`
   ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_X_ASSUM(fun ih -> if is_forall(concl ih) then
       MP_TAC(SPECL [`childfam (Wf:(num->int)->num->int->int) t (pp 0) b`;
         `\j:num. (pp:num->num->num)(j+1)`; `B:num`] ih) else NO_TAC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `bp:num->bool` THEN
      FIRST_X_ASSUM(fun th -> if (try free_in `SUC s` (concl th) with _ ->
       false) then MP_TAC(SPEC `\n:num. if n = 0 then b else
        (bp:num->bool)(n-1)` th) else NO_TAC) THEN
      REWRITE_TAC[PLEAF_CONS];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(pp:num->num->num) 0`; `t:num`; `M:int`;
    `Wf:(num->int)->num->int->int`; `HH:(num->int)->bool`] GEN_FOLD) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXP] THEN DISCH_TAC THEN
  MATCH_MP_TAC TOWER_ARITH THEN
  EXISTS_TAC `nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
   isum(1..2*t)(\i. signfam (\k. (Wf:(num->int)->num->int->int) hh ((pp 0) k))
    t i (w i)) = &0})` THEN
  EXISTS_TAC `nsum HH (\hh. CARD {w | w IN ibox (2*t) M /\
   isum(1..2*t)(\i. signfam (\j. (Wf:(num->int)->num->int->int) hh ((pp
    0)(j+t))) t i (w i)) = &0})` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `F`) THEN REWRITE_TAC[CHILDFAM] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `T`) THEN REWRITE_TAC[CHILDFAM] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[]]);;

let ABS_INT_HAS_SIZE = prove
 (`!M:int. &0 <= M ==> {v:int | abs v <= M} HAS_SIZE (2 * num_of_int M + 1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:int | abs v <= M} = {k:int | --M <= k /\ k <= M}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN INT_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[HAS_SIZE; FINITE_INT_SEG; EXACT_INT_INTERVAL_CARD;
               INT_ARITH `&0 <= M ==> --M:int <= M`] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD;
              GSYM INT_OF_NUM_MUL] THEN
  ASM_SIMP_TAC[INT_OF_NUM_OF_INT; INT_ARITH
   `&0 <= M ==> &0:int <= M - --M + &1`] THEN
  ASM_INT_ARITH_TAC);;

let INT_ONE_LE_MUL = prove
 (`!a b:int. &1 <= a /\ &1 <= b ==> &1 <= a * b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `a:int` THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_RID] THEN
  MATCH_MP_TAC INT_LE_LMUL THEN ASM_INT_ARITH_TAC);;

let EXP_ID_MSUPP_GE2 = prove
 (`!(e:num) (G:num). 2 <= e /\ e-1 <= G
     ==> (G-(e-1))*(2*e) + (2*e*G - 2*e) = 2*(2*e*G) - e*(2*e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?q. G = q + (e-1)` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `G-(e-1)` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?r. e = r+2` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `e-2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(r+2)-1 = r+1`; ARITH_RULE `(q+r+1)-(r+1) = q`] THEN
  SUBGOAL_THEN `2*(r+2) <= 2*(r+2)*(q+r+1) /\
   (r+2)*2*(r+2) <= 2*2*(r+2)*(q+r+1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `2*(r+2) = 2*(r+2)*1`] THEN
      REWRITE_TAC[GSYM MULT_ASSOC] THEN MATCH_MP_TAC LE_MULT2 THEN ARITH_TAC;
      REWRITE_TAC[ARITH_RULE `2*2*(r+2)*x = (2*(r+2))*(2*x) /\
       (r+2)*2*(r+2) = (2*(r+2))*(r+2)`] THEN
      MATCH_MP_TAC LE_MULT2 THEN ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_EQ; GSYM INT_OF_NUM_ADD] THEN
   ASM_SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_ADD] THEN
   CONV_TAC INT_RING);;

let POW_MSUPP_COMBINE_GE2 = prove
 (`!(e:num) (G:num) (P:int). 2 <= e /\ e-1 <= G
     ==> (P pow (G-(e-1))) pow (2*e) * P pow (2*e*G - 2*e) = P pow (2*(2*e*G) -
      e*(2*e))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[INT_POW_POW; GSYM INT_POW_ADD] THEN
  AP_TERM_TAC THEN ASM_SIMP_TAC[EXP_ID_MSUPP_GE2]);;

let EXP_COMBINE_GE2 = prove
 (`!(e:num) (kk:num) (P:int). &1 <= P /\ 2 <= e /\ e*(2*e) <= 2*kk
     ==> P pow (2*kk - e*(2*e)) * ((&2 * P) * &2 * (&2 * P) pow (e-1)) pow (2*e
      - 1) = (&2 pow (e+1)) pow (2*e-1) * P pow (2*kk - e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `((&2 * (P:int)) * &2 * (&2 * P) pow (e-1)) =
    &2 pow (e+1) * P pow e`
   SUBST1_TAC THENL
   [SUBGOAL_THEN
     `(&2 * (P:int)) pow (e-1) = &2 pow (e-1) * P pow (e-1)`
    SUBST1_TAC THENL [REWRITE_TAC[INT_POW_MUL]; ALL_TAC] THEN
    SUBGOAL_THEN `(P:int) pow e = P pow 1 * P pow (e-1) /\
     (&2:int) pow (e+1) = &2 pow 2 * &2 pow (e-1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[INT_POW_1] THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_POW_MUL; INT_POW_POW] THEN
  ONCE_REWRITE_TAC[INT_ARITH `a * b * c = b * (a * c):int`] THEN
  AP_TERM_TAC THEN REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `e*(2*e-1) = e*(2*e) - e` SUBST1_TAC THENL
   [REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES]; ALL_TAC] THEN
  MATCH_MP_TAC SUBADD_ID THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `e <= e*(2*e)` MP_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `e*1` THEN CONJ_TAC THENL
     [REWRITE_TAC[MULT_CLAUSES; LE_REFL];
      MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let TELESCOPE_CLOSE_GE2 = prove
 (`!(e:num) (G:num) (P:int) (Cm:int) (Cf:int).
     2 <= e /\ e-1 <= G /\ &1 <= P
     ==> (Cm pow (2*e)) * (P pow (G-(e-1))) pow (2*e) * P pow (2*e*G - 2*e) *
         (Cf * ((&2 * P) * &2 * (&2 * P) pow (e-1)) pow (2*e-1))
       = (Cm pow (2*e) * Cf * (&2 pow (e+1)) pow (2*e-1)) * P pow (2*(2*e*G) -
        e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`P:int`] POW_MSUPP_COMBINE_GE2) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[INT_ARITH `a * b * c * d = a * (b * c)
   * d:int`] THEN REWRITE_TAC[th]) THEN
  MP_TAC(SPECL [`e:num`;`2*e*G:num`;`P:int`] EXP_COMBINE_GE2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e <= 2*G` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `2*(2*e*G) = e*(2*2*G)`;
      ARITH_RULE `e*(2*e) = e*(2*e)`] THEN
    MATCH_MP_TAC LE_MULT2 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th ->
    ONCE_REWRITE_TAC[INT_ARITH `Cm * pp * Cf * fam = Cf * (pp * fam) * Cm:int`]
     THEN
    REWRITE_TAC[th]) THEN
  INT_ARITH_TAC);;

let DP_RED_TO_CLOSE_GE2 = prove
 (`!e (G:num) (P:int) (Cm:int) (Cf:int) (FS:num).
     2 <= e /\ e-1 <= G /\ &1 <= P /\ &1 <= Cm /\ &1 <= Cf /\
     &FS <= Cm pow (2*e) * (P pow (G-(e-1))) pow (2*e) * P pow (2*e*G - 2*e) *
            (Cf * ((&2 * P) * &2 * (&2 * P) pow (e-1)) pow (2*e-1))
     ==> &FS <= (Cm pow (2*e) * Cf * (&2 pow (e+1)) pow (2*e-1)) * P pow
      (2*(2*e*G) - e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`P:int`;`Cm:int`;`Cf:int`] TELESCOPE_CLOSE_GE2)
   THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SYM th)) THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN
  ASM_REWRITE_TAC[]);;

let CARD_2E_GT2 = prove
 (`!e. 2 <= e ==> 2 < CARD(1..(2*e))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CARD_NUMSEG_1] THEN ASM_ARITH_TAC);;

let GROUPED_TO_3FACTOR_UNIF = prove
 (`!(s:num->bool) (mult:num->int->num) (MaxMult:num) A B (Cf:int).
     FINITE s /\ 2 < CARD s /\ &1 <= A /\ A <= &2 * B /\
      &2 * B <= A pow (CARD s - 1) /\
     (!i z. mult i z <= MaxMult) /\
     (!mfn:(num->int)->int.
         isum {a:num->int | (!i. i IN s ==> abs(a i) <= A) /\
          (!i. ~(i IN s) ==> a i = &0)}
              (\a. &(lincount s a (mfn a) B))
         <= Cf * (A * &2 * B) pow (CARD s - 1))
     ==> &(nsum {hh:num->int | (!i. i IN s ==> abs(hh i) <= A) /\
      (!i. ~(i IN s) ==> hh i = &0)}
                  (\hh. nsum {z:num->int | (!i. i IN s ==> abs(z i) <= B) /\
                   (!i. ~(i IN s) ==> z i = &0) /\
                                           isum s (\i. hh i * z i) = &0}
                             (\z. nproduct s (\i. mult i (z i)))))
             <= &(MaxMult EXP (CARD s)) * Cf * (A * &2 * B) pow (CARD s - 1)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum {hh:num->int | (!i. i IN s ==> abs(hh i) <= A) /\
   (!i. ~(i IN s) ==> hh i = &0)}
                   (\hh. &(MaxMult EXP (CARD(s:num->bool))) * &(lincount s hh
                    (&0) B))` THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `FINITE {hh:num->int | (!i. i IN s ==> abs(hh i) <= A) /\
    (!i. ~(i IN s) ==> hh i = &0)}` ASSUME_TAC THENL
     [MATCH_MP_TAC COEFFBOX_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_OF_NUM_ISUM] THEN
    MATCH_MP_TAC ISUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `hh:num->int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    MP_TAC(ISPECL
     [`s:num->bool`;`hh:num->int`;`&0:int`;`B:int`;`mult:num->int->num`;
       `MaxMult:num`] WEIGHTED_LINEAR_BND) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_LE] THEN
    DISCH_THEN(fun th -> MATCH_MP_TAC INT_LE_TRANS THEN
     EXISTS_TAC (rand(concl th)) THEN CONJ_TAC THENL
      [ALL_TAC; ASM_REWRITE_TAC[INT_LE_REFL]]) THEN
    ASM_REWRITE_TAC[INT_OF_NUM_LE; INT_OF_NUM_MUL];
    REWRITE_TAC[ISUM_CONST_LINCOUNT] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_POS];
      FIRST_X_ASSUM(MP_TAC o SPEC `(\a. &0):(num->int)->int`) THEN
       REWRITE_TAC[]]]);;

let WIDE_LINFAC_FACTOR = prove
 (`!(P:int) (e:num) (W:int). 2 <= e /\ &1 <= P
   ==> (&2 * P) * &2 * (W * (&2 * P) pow (e-1)) = W * &2 pow (e+1) * P pow e`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[INT_POW_MUL] THEN
  SUBGOAL_THEN
   `(&2:int) pow (e+1) = &2 * &2 * &2 pow (e-1) /\
    (P:int) pow e = P * P pow (e-1)`
   STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM(CONJUNCT2 INT_POW)] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let GN_UNIF_BND_GEN = prove
 (`!(mult:num->int->num) (MaxMult:num) (P:int) (e:num) (Cf:int) (Cfp:int)
  (B:int).
     2 <= e /\ &1 <= P /\ Cf <= Cfp /\ &2 * P <= &2 * B /\
      &2 * B <= (&2 * P) pow (2*e-1) /\
     (!i z. mult i z <= MaxMult) /\
     (!A B' mfn.
        &1 <= A /\ A <= &2 * B' /\ &2 * B' <= A pow (CARD (1..2 * e) - 1)
        ==> isum {a | (!i. i IN 1..2 * e ==> abs (a i) <= A) /\
         (!i. ~(i IN 1..2 * e) ==> a i = &0)}
                 (\a. &(lincount (1..2 * e) a (mfn a) B')) <= Cf * (A * &2 *
                  B') pow (CARD (1..2 * e) - 1))
     ==> &(nsum {hh | (!i. i IN 1..(2*e) ==> abs(hh i) <= (&2*P)) /\
      (!i. ~(i IN 1..(2*e)) ==> hh i = &0)}
                (\hh. nsum {z | (!i. i IN 1..(2*e) ==> abs(z i) <= B) /\
                 (!i. ~(i IN 1..(2*e)) ==> z i = &0) /\
                                isum (1..(2*e)) (\i. hh i * z i) = &0}
                           (\z. nproduct (1..(2*e)) (\i. mult i (z i)))))
         <= &(MaxMult EXP (2*e)) * Cfp * ((&2 * P) * &2 * B) pow (2*e-1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= &2 * (P:int) /\ &2 * P <= &2 * B /\
   &2 * B <= (&2 * P) pow (2*e-1)` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= ((&2 * (P:int)) * &2 * B) pow (2*e-1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE THEN MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ASM_INT_ARITH_TAC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1..(2*e)`; `mult:num->int->num`; `MaxMult:num`;
    `(&2 * P):int`; `B:int`; `Cfp:int`] GROUPED_TO_3FACTOR_UNIF) THEN
  REWRITE_TAC[FINITE_NUMSEG; CARD_NUMSEG_1] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      X_GEN_TAC `mfn:(num->int)->int` THEN
      MATCH_MP_TAC INT_LE_TRANS THEN
       EXISTS_TAC
        `(Cf:int) * ((&2 * P) * &2 * B) pow (2*e-1)` THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPECL [`(&2 *
        P):int`;`B:int`;`mfn:(num->int)->int`]) THEN
        REWRITE_TAC[CARD_NUMSEG_1] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[CARD_NUMSEG_1]]);;

let DP_RED_TO_CLOSE_WIDE = prove
 (`!e (G:num) (P:int) (Cm:int) (Cf:int) (W:int) (FS:num).
     2 <= e /\ e-1 <= G /\ &1 <= P /\ &1 <= Cm /\ &1 <= Cf /\ &1 <= W /\
     &FS <= Cm pow (2*e) * (P pow (G-(e-1))) pow (2*e) * P pow (2*e*G - 2*e) *
            (Cf * ((&2 * P) * &2 * (W * (&2 * P) pow (e-1))) pow (2*e-1))
     ==> &FS <= (Cm pow (2*e) * (Cf * W pow (2*e-1)) * (&2 pow (e+1)) pow
      (2*e-1)) * P pow (2*(2*e*G) - e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:num`;`G:num`;`P:int`;`Cm:int`;`(Cf:int) * (W:int) pow
   (2*e-1)`;`FS:num`] DP_RED_TO_CLOSE_GE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_ONE_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_POW_LE_1 THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if free_in `FS:num` (concl th) then MP_TAC th else
   NO_TAC) THEN
  MP_TAC(SPECL [`P:int`;`e:num`;`W:int`] WIDE_LINFAC_FACTOR) THEN
   ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; INT_POW_MUL]) THEN
  MATCH_MP_TAC(INT_ARITH
   `(x:int) = y ==> &FS <= x ==> &FS <= y`) THEN
   CONV_TAC INT_RING);;

let FIBER_LINSUM_PARTITION = prove
 (`!(S:(num->int)->bool) (Bvec:(num->int)->num->int) (w:num->int) (m:num).
     FINITE S
     ==> CARD {y | y IN S /\ isum(0..m-1)(\g. w g * Bvec y g) = &0} =
         nsum (IMAGE (\y. (\g. Bvec y g)) S)
              (\zv. if isum(0..m-1)(\g. w g * zv g) = &0
                    then CARD {y | y IN S /\ (\g. Bvec y g) = zv} else 0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `CARD {y:num->int | y IN S /\ isum(0..m-1)(\g. w g * Bvec y g) = &0} =
    nsum S (\y:num->int. if isum(0..m-1)(\g. (w:num->int) g * Bvec y g) = &0
     then 1 else 0)`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `{y:num->int | y IN S /\
    isum(0..m-1)(\g. w g * Bvec y g) = &0} =
                  {y | y IN S /\
                   (\y. isum(0..m-1)(\g. (w:num->int) g * Bvec y g) = &0) y}`
      SUBST1_TAC THENL [REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT] THEN
     REWRITE_TAC[NSUM_RESTRICT_SET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\y:num->int. (\g. Bvec y g):num->int`;
                 `\y:num->int. if isum(0..m-1)(\g. (w:num->int) g * Bvec y g) =
                  &0 then 1 else 0`;
                 `S:(num->int)->bool`] NSUM_IMAGE_GEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `zv:num->int` THEN
  REWRITE_TAC[IN_IMAGE] THEN
   DISCH_THEN(X_CHOOSE_THEN `x0:num->int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE {y:num->int | y IN S /\
   (\g. Bvec y g) = (zv:num->int)}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `S:(num->int)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `nsum {y:num->int | y IN S /\ (\g. Bvec y g) = (zv:num->int)}
         (\y. if isum(0..m-1)(\g. (w:num->int) g * Bvec y g) = &0 then 1 else
          0) =
    nsum {y:num->int | y IN S /\ (\g. Bvec y g) = (zv:num->int)}
         (\y. if isum(0..m-1)(\g. (w:num->int) g * zv g) = &0 then 1 else 0)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `y:num->int` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `isum(0..m-1)(\g. (w:num->int) g * Bvec (y:num->int) g) =
     isum(0..m-1)(\g. w g * (zv:num->int) g)`
      (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `g:num` THEN DISCH_TAC THEN
     REWRITE_TAC[] THEN
    AP_TERM_TAC THEN
    UNDISCH_TAC `(\g. Bvec (y:num->int) g) = (zv:num->int)` THEN
    REWRITE_TAC[FUN_EQ_THM] THEN DISCH_THEN(MP_TAC o SPEC `g:num`) THEN
     REWRITE_TAC[];
    ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[NSUM_0] THEN
  ASM_SIMP_TAC[NSUM_CONST] THEN REWRITE_TAC[MULT_CLAUSES]);;

let NPROD_MAXMULT = prove
 (`!(cnt:num->num) (MaxMult:num) (e:num).
     (!g. g < 2*e ==> cnt g <= MaxMult)
     ==> nproduct {g | g < 2*e} cnt <= MaxMult EXP (2*e)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nproduct {g | g < 2*e} (\g:num. MaxMult)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC NPRODUCT_LE THEN
    REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[NPRODUCT_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT; LE_REFL]]);;

let LEAF_PERX_BND = prove
 (`!(S:(num->int)->bool) (Bvec:(num->int)->num->int) (w:num->int) (e:num)
     (perblk:num->int->num) (MaxMult:num) (boxset:(num->int)->bool).
      FINITE S /\ FINITE boxset /\
      (!zv. zv IN IMAGE (\y. (\g. Bvec y g)) S
            ==> CARD {y | y IN S /\ (\g. Bvec y g) = zv} =
                nproduct {g | g < 2*e} (\g. perblk g (zv g))) /\
      (!g v. g < 2*e ==> perblk g v <= MaxMult) /\
      (!y. y IN S ==> (\g. Bvec y g) IN boxset)
      ==> CARD {y | y IN S /\ isum(0..(2*e)-1)(\g. w g * Bvec y g) = &0} <=
          nsum boxset (\zv. if isum(0..(2*e)-1)(\g. w g * zv g) = &0
                            then MaxMult EXP (2*e) else 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:(num->int)->bool`; `Bvec:(num->int)->num->int`;
    `w:num->int`; `2*e`]
                FIBER_LINSUM_PARTITION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC
   `nsum (IMAGE (\y:num->int. (\g. Bvec y g)) S)
         (\zv. if isum(0..(2*e)-1)(\g. w g * zv g) = &0 then MaxMult EXP (2*e)
          else 0)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    X_GEN_TAC `zv:num->int` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN REWRITE_TAC[LE_REFL] THEN
    SUBGOAL_THEN `CARD {y:num->int | y IN (S:(num->int)->bool) /\
     (\g:num. (Bvec:(num->int)->num->int) y g) = (zv:num->int)} =
                  nproduct {g | g < 2*e} (\g. (perblk:num->int->num) g (zv g))`
      SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC NPROD_MAXMULT THEN ASM_SIMP_TAC[];
    MATCH_MP_TAC NSUM_SUBSET THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN
    X_GEN_TAC `zv:num->int` THEN REWRITE_TAC[IN_DIFF; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y0:num->int`
     STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(zv:num->int) IN boxset` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `zv:num->int` with _ ->
     false)
                            then SUBST1_TAC th else NO_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y0:num->int`) THEN ASM_REWRITE_TAC[]]);;

let VAC_IF_SUM = prove
 (`!(e:num) (w:num->int) (Fv:num->int).
     0 < e
     ==> isum(0..(2*e)-1)(\g. w g * (if g < 2*e then Fv g else &0)) =
      isum(0..(2*e)-1)(\g. w g * Fv g)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `g:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `g < 2*e` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC);;

let TRUNC_FIBER_EQ = prove
 (`!e (t:num) (M:int) (W:num->num->int->int) (zv:num->int).
     (!g. ~(g < 2*e) ==> zv g = &0)
     ==> {y | y IN ibox ((2*e)*t) M /\
              (\g. if g < 2*e then isum(1..t)(\i. W g i (y (g*t+i))) else &0) =
               zv} =
         {y | y IN ibox ((2*e)*t) M /\
              (!g. g < 2*e ==> isum(1..t)(\i. W g i (y (g*t+i))) = zv g)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   X_GEN_TAC `y:num->int` THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  REWRITE_TAC[FUN_EQ_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `g:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `g:num`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN X_GEN_TAC `g:num` THEN COND_CASES_TAC THEN
     ASM_SIMP_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
     ASM_REWRITE_TAC[]]);;

let PERHH_MBLOCK_BND = prove
 (`!e (t:num) (M:int) (W:num->num->int->int) (w:num->int) (MaxMult:num)
  (boxset:(num->int)->bool).
     0 < e /\ FINITE boxset /\
     (!g v. g < 2*e ==> CARD {u | u IN ibox t M /\
      isum(1..t)(\i. W g i (u i)) = v} <= MaxMult) /\
     (!y. y IN ibox ((2*e)*t) M ==> (\g. if g < 2*e then isum(1..t)(\i. W g i
      (y (g*t+i))) else &0) IN boxset)
     ==> CARD {y | y IN ibox ((2*e)*t) M /\
                   isum(0..(2*e)-1)(\g. w g * isum(1..t)(\i. W g i (y
                    (g*t+i)))) = &0}
         <= nsum boxset (\zv. if isum(0..(2*e)-1)(\g. w g * zv g) = &0 then
          MaxMult EXP (2*e) else 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
    [`ibox ((2*e)*t) M`;
     `\(y:num->int) (g:num). if g < 2*e then isum(1..t)(\i.
      (W:num->num->int->int) g i (y (g*t+i))) else &0`;
     `w:num->int`; `e:num`;
     `\(g:num) (v:int). CARD {u | u IN ibox t M /\
      isum(1..t)(\i. (W:num->num->int->int) g i (u i)) = v}`;
     `MaxMult:num`; `boxset:(num->int)->bool`]
    LEAF_PERX_BND) THEN
  REWRITE_TAC[IBOX_FINITE] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `zv:num->int` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!g. ~(g < 2*e) ==> (zv:num->int) g = &0` ASSUME_TAC THENL
     [UNDISCH_TAC `zv IN IMAGE (\y g. if g < 2*e then isum(1..t)(\i.
      (W:num->num->int->int) g i (y (g*t+i))) else &0) (ibox ((2*e)*t) M)` THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `x0:num->int` (CONJUNCTS_THEN2 (SUBST1_TAC)
       ASSUME_TAC)) THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[TRUNC_FIBER_EQ] THEN
    MP_TAC(ISPECL [`\(g:num) (i:num) (x:int). (W:num->num->int->int) g i x`;
      `t:num`; `M:int`; `zv:num->int`; `2*e`] MBLOCK_FIBER_CARD) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
     REFL_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[VAC_IF_SUM]);;

let BLOCK_ARITH3 = prove
 (`!e (G:num). 1 <= e ==> (2*e-1)*G + G = 2*e*G`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MULT_ASSOC] THEN
  SUBGOAL_THEN `(2 * e) * G = ((2*e-1)+1) * G` SUBST1_TAC THENL
   [AP_THM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    REWRITE_TAC[RIGHT_ADD_DISTRIB; MULT_CLAUSES]]);;

let BLOCK_INJ_ARITH = prove
 (`!p1 p2 q1 q2 (G:num). 1 <= p2 /\ p2 <= G /\ 1 <= q2 /\ q2 <= G /\
  p1*G+p2 = q1*G+q2 ==> p1 = q1 /\ p2 = q2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`p1*G+(p2-1)`; `G:num`; `p1:num`; `p2-1`; `q1:num`;
    `q2-1`] DIVMOD_UNIQ_LEMMA) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
    [ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC];
    ASM_ARITH_TAC]);;

let BLOCK_UB = prove
 (`!p1 p2 e (G:num). 1 <= e /\ p1 <= 2*e-1 /\ p2 <= G ==> p1*G+p2 <= 2*e*G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`] BLOCK_ARITH3) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC LE_ADD2 THEN
  ASM_REWRITE_TAC[LE_MULT_RCANCEL]);;

let BLOCK_IMAGE_EQ = prove
 (`!e (G:num). 1 <= e /\
  1 <= G ==> IMAGE (\(i,j). i*G+j) {i,j | i IN 0..2 * e - 1 /\
   j IN 1..G} = 1..2*e*G`,
  REPEAT STRIP_TAC THEN
   REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM;
     IN_NUMSEG] THEN
  X_GEN_TAC `n:num` THEN CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN
   EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
    [ASM_ARITH_TAC;
      MP_TAC(SPECL [`p1:num`;`p2:num`;`e:num`;`G:num`] BLOCK_UB) THEN
       ASM_REWRITE_TAC[]];
    MAP_EVERY EXISTS_TAC [`(n-1) DIV G`; `(n-1) MOD G + 1`] THEN
    MP_TAC(SPECL [`n-1`;`G:num`] DIVISION) THEN
    ASM_SIMP_TAC[ARITH_RULE `1 <= G ==> ~(G = 0)`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(n-1) DIV G < 2*e` ASSUME_TAC THENL
     [ASM_SIMP_TAC[RDIV_LT_EQ; ARITH_RULE `1 <= G ==> ~(G = 0)`] THEN
      ONCE_REWRITE_TAC[MULT_SYM] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC; ARITH_TAC;
       ASM_ARITH_TAC]]);;

let BLOCK_MAP_INJ = prove
 (`!e (G:num). 1 <= G ==> (!x y. x IN {i,j | i IN 0..2 * e - 1 /\ j IN 1..G} /\
  y IN {i,j | i IN 0..2 * e - 1 /\ j IN 1..G} /\
   (\(i,j). i*G+j) x = (\(i,j). i*G+j) y ==> x = y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; IN_NUMSEG] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`p1:num`;`p2:num`;`p1':num`;`p2':num`;`G:num`] BLOCK_INJ_ARITH)
   THEN
  ASM_REWRITE_TAC[PAIR_EQ]);;

let ISUM_BLOCK_REGROUP = prove
 (`!e (G:num) (H:num->int). 1 <= e /\ 1 <= G ==>
     isum(1..2*e*G) H = isum(0..2*e-1)(\g. isum(1..G)(\i. H(g*G+i)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`0..2*e-1`; `\g:num. 1..G`;
    `\g i. (H:num->int)(g*G+i)`] ISUM_ISUM_PRODUCT) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`] BLOCK_IMAGE_EQ) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(SPECL [`e:num`;`G:num`] BLOCK_MAP_INJ) THEN ASM_REWRITE_TAC[] THEN
   DISCH_TAC THEN
  MP_TAC(ISPECL [`(\(i,j). i*G+j):num#num->num`; `H:num->int`;
    `{i,j | i IN 0..2 * e - 1 /\ j IN 1..G}`] ISUM_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC ISUM_EQ THEN
   REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; o_THM] THEN
  CONV_TAC(TOP_DEPTH_CONV GEN_BETA_CONV) THEN REWRITE_TAC[]);;

let DEC_FACT = prove
 (`!x e (G:num). 1 <= G /\ x IN 1..2*e*G ==> (x-1) DIV G < 2*e /\
  (x-1) MOD G < G`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(G = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_SIMP_TAC[RDIV_LT_EQ; MOD_LT_EQ] THEN
  SUBGOAL_THEN `G * 2 * e = 2 * e * G` SUBST1_TAC THENL
   [CONV_TAC NUM_RING; ASM_ARITH_TAC]);;

let LEAF_BLOCK_PERM = prove
 (`!e ss (G:num) (lab:num->num) (en:num->num->num).
     2 <= e /\ e-1 <= ss /\ 1 <= G /\ G = 2 EXP ss /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
     (!g r. g < 2*e /\ r < G ==> en g r IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g r) = lab g) /\
     (!g i. g < 2*e /\ i IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g ==> ?!r. r < G /\
       en g r = i)
     ==> (\j. if j IN 1..2*e*G then en ((j-1) DIV G) ((j-1) MOD G) else j)
      permutes 1..2*e*G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
   SIMP_TAC[PERMUTES_FINITE_INJECTIVE; FINITE_NUMSEG] THEN
  SUBGOAL_THEN `!g1 r1 g2 r2. g1 < 2*e /\ r1 < G /\ g2 < 2*e /\ r2 < G /\
   (en:num->num->num) g1 r1 = en g2 r2 ==> g1 = g2 /\
    r1 = r2` (LABEL_TAC "INJ") THENL
   [MATCH_MP_TAC LEAF_BLOCK_INJ THEN
    MAP_EVERY EXISTS_TAC [`ss:num`; `lab:num->num`] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`x:num`;`e:num`;`G:num`] DEC_FACT) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`x:num`;`y:num`] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`x:num`;`e:num`;`G:num`] DEC_FACT) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(SPECL [`y:num`;`e:num`;`G:num`] DEC_FACT) THEN
     ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (is_eq o concl)) THEN ASM_REWRITE_TAC[] THEN
     DISCH_TAC THEN
    USE_THEN "INJ" (MP_TAC o SPECL [`(x-1) DIV G`;`(x-1) MOD G`;`(y-1) DIV
     G`;`(y-1) MOD G`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `~(G = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`x-1`;`G:num`] DIVISION) THEN
     MP_TAC(SPECL [`y-1`;`G:num`] DIVISION) THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC]);;

let PERTERM = prove
 (`!(fj:int) (x:int) (M:int) (cpsi:int) (d:num) (j:num).
     &1 <= M /\ abs x <= M /\ &1 <= cpsi /\ j <= d /\
      abs fj <= cpsi * M pow (d - j)
     ==> abs(fj * x pow j) <= cpsi * M pow d`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= (M:int) /\ &0 <= (cpsi:int) /\ &0 <= abs x /\
    abs x <= M`
   STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[INT_ABS_POS] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[INT_ABS_MUL; INT_ABS_POW] THEN
  SUBGOAL_THEN
   `(cpsi:int) * M pow d = (cpsi * M pow (d-j)) * M pow j`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_MUL_ASSOC; GSYM INT_POW_ADD] THEN
    AP_TERM_TAC THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
    MATCH_MP_TAC INT_LE_MUL2 THEN
    ASM_SIMP_TAC[INT_ABS_POS; INT_POW_LE] THEN
    MATCH_MP_TAC INT_POW_LE2 THEN ASM_REWRITE_TAC[INT_ABS_POS]]);;

let IPOLY_ABS_BOUND = prove
 (`!(f:num->int) d (x:int) (M:int) (cpsi:int).
      &1 <= M /\ abs x <= M /\ &1 <= cpsi /\
       (!j. j <= d ==> abs(f j) <= cpsi * M pow (d - j))
      ==> abs(ipoly f d x) <= &(d+1) * cpsi * M pow d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[ipoly] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum(0..d)(\j. abs((f:num->int) j * x pow j))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC ISUM_ABS THEN
   REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum(0..d)(\j:num. cpsi * M pow d)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `j:num` THEN STRIP_TAC THEN MATCH_MP_TAC PERTERM THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[ISUM_CONST; FINITE_NUMSEG; CARD_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(d+1)-0 = d+1`] THEN
     MATCH_ACCEPT_TAC INT_LE_REFL]);;

let LEAF_COUNT_RESHAPE = prove
 (`!e ss (G:num) (P:int) (PSI:(num->int)->num->num->int) (hh:num->int)
  (lab:num->num) (en:num->num->num).
     2 <= e /\ e-1 <= ss /\ 1 <= G /\ G = 2 EXP ss /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
     (!g r. g < 2*e /\ r < G ==> en g r IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g r) = lab g) /\
     (!g i. g < 2*e /\ i IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g ==> ?!r. r < G /\
       en g r = i)
     ==> CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh
                    i) (e-1) y) (e*G) (\j. RIFFLE(e*G)) (\j. F) hh i (y i)) =
                     &0} =
         CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(0..2*e-1)(\g. hh(lab g) * isum(1..G)(\i. (if leafsg ss
                    (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g (i-1)) then --(ipoly
                     (PSI hh (lab g)) (e-1) (y(g*G+i))) else ipoly (PSI hh (lab
                      g)) (e-1) (y(g*G+i))))) = &0}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PLEAF_SGNRELAB; SGNRELAB] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `(\j. if j IN 1..2*e*G then en ((j-1) DIV G) ((j-1) MOD G) else
   j) permutes 1..2*e*G` ASSUME_TAC THENL
   [MATCH_MP_TAC LEAF_BLOCK_PERM THEN
    MAP_EVERY EXISTS_TAC [`ss:num`;`lab:num->num`] THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(\j. if j IN 1..2*e*G then en ((j-1) DIV G) ((j-1) MOD G)
   else j):num->num`; `2*e*G`; `&2*P:int`;
     `\i x. if leafsg ss (e*G) (\j. RIFFLE(e*G)) (\j. F) i then --(hh (leafidx
      ss (e*G) (\j. RIFFLE(e*G)) (\j. F) i) * ipoly (PSI hh (leafidx ss (e*G)
       (\j. RIFFLE(e*G)) (\j. F) i)) (e-1) x) else hh (leafidx ss (e*G) (\j.
        RIFFLE(e*G)) (\j. F) i) * ipoly (PSI hh (leafidx ss (e*G) (\j.
         RIFFLE(e*G)) (\j. F) i)) (e-1) x`] FIBER_PERMUTE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `G = 2 EXP ss` then REWRITE_TAC[SYM th]
   else NO_TAC) THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   X_GEN_TAC `y:num->int` THEN
  MATCH_MP_TAC(TAUT `(a ==> (b <=> c)) ==> (a /\ b <=> a /\ c)`) THEN
   DISCH_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  W(fun (asl,w) -> let lhs_tm = lhand w in let hfun = rand lhs_tm in
   MP_TAC(ISPECL [`e:num`; `G:num`; hfun] ISUM_BLOCK_REGROUP)) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST_ASSUM(fun th -> if concl th = `G = 2 EXP ss` then REWRITE_TAC[SYM th]
   else NO_TAC) THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `g:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THEN
  REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC ISUM_EQ THEN
   X_GEN_TAC `i:num` THEN
  REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
  SUBGOAL_THEN `1 <= e` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `1 <= g * G + i /\
   g * G + i <= 2 * e * G` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_ARITH_TAC;
      MP_TAC(SPECL [`g:num`;`i:num`;`e:num`;`G:num`] BLOCK_UB) THEN
       ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(SPECL [`(g*G+i)-1`; `G:num`; `g:num`; `i-1`] DIVMOD_UNIQ) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if concl th = `G = 2 EXP ss` then REWRITE_TAC[SYM th]
   else NO_TAC) THEN
  FIRST_ASSUM(fun th -> match (try Some(SPECL [`g:num`;`i-1`] th) with _ ->
   None) with Some th' when (let c = concl th' in is_imp c && (try
    (is_conj(snd(dest_imp c)) && rand(snd(dest_imp c)) = `leafidx ss (e * G)
     (\j. RIFFLE(e*G)) (\j. F) (en g (i-1)) = (lab:num->num) g`) with _ ->
      false)) -> ASSUME_TAC th' | _ -> NO_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) && (try
   is_conj(snd(dest_imp(concl th))) with _ -> false))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN INT_ARITH_TAC);;

let FINITE_GBOX = prove
 (`!(n:num) (B:int). FINITE {zv:num->int | (!g. g < n ==> abs(zv g) <= B) /\
  (!g. ~(g < n) ==> zv g = &0)}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `IMAGE (\z:num->int. (\g. z (g+1))) (ibox n B)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN REWRITE_TAC[IBOX_FINITE];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
     X_GEN_TAC `zv:num->int` THEN
    STRIP_TAC THEN
    EXISTS_TAC `\i:num. if i IN 1..n then (zv:num->int)(i-1) else &0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `g:num` THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC[IN_NUMSEG; ADD_SUB] THEN
      ASM_CASES_TAC `g < n:num` THENL
       [SUBGOAL_THEN `1 <= g + 1 /\
        g + 1 <= n` (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `~(1 <= g + 1 /\
         g + 1 <= n)` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      REWRITE_TAC[ibox; IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[IN_NUMSEG] THENL
       [SUBGOAL_THEN `1 <= i /\ i <= n` (fun th -> REWRITE_TAC[th]) THENL
         [ASM_ARITH_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
        SUBGOAL_THEN `~(1 <= i /\ i <= n)` (fun th -> REWRITE_TAC[th]) THEN
         ASM_ARITH_TAC]]]);;

let TSET_IN_RANGE = prove
 (`!e (G:num) t. 1 <= G /\ t IN TSET e G ==> t IN 1..2*e*G`,
  REWRITE_TAC[TSET; IN_UNION; IN_IMAGE; IN_NUMSEG] THEN REPEAT STRIP_TAC THENL
   [ASM_ARITH_TAC;
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `e*G:num` THEN CONJ_TAC THENL
     [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `e*1` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[LE_MULT_LCANCEL] THEN
        ASM_ARITH_TAC]; ASM_ARITH_TAC];
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC(ARITH_RULE `x <= e*G ==> e*G+x <= 2*e*G`) THEN
     MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `e*1` THEN CONJ_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]]);;

let BLOCK_IN_WBOX = prove
 (`!e ss (G:num) (P:int) (cpsi:int) (PSI:(num->int)->num->num->int)
  (hh:num->int) (lab:num->num) (en:num->num->num).
     2 <= e /\ 1 <= G /\ &1 <= P /\ &1 <= cpsi /\
     (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) /\ j <= (e-1)
          ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
     (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
     (!g. g < 2*e ==> lab g IN TSET e G)
     ==> !y. y IN ibox (2*e*G) (&2*P)
         ==> (\g. if g < 2*e then isum(1..G)(\i. if leafsg ss (e*G) (\j.
          RIFFLE(e*G)) (\j. F) (en g (i-1)) then --ipoly (PSI hh (lab g)) (e-1)
           (y(g*G+i)) else ipoly (PSI hh (lab g)) (e-1) (y(g*G+i))) else &0)
             IN {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi * (&2*P) pow
              (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  X_GEN_TAC `g:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `isum(1..G)(\i:num. abs(if leafsg ss (e*G) (\j. RIFFLE(e*G)) (\j.
   F) ((en:num->num->num) g (i-1)) then --ipoly (PSI (hh:num->int)
    ((lab:num->num) g)) (e-1) (y(g*G+i)) else ipoly (PSI hh (lab g)) (e-1)
     (y(g*G+i))))` THEN
  CONJ_TAC THENL [MATCH_MP_TAC ISUM_ABS THEN
   REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
   EXISTS_TAC `isum(1..G)(\i:num. &e * cpsi * (&2*P) pow (e-1))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC ISUM_LE THEN REWRITE_TAC[FINITE_NUMSEG; IN_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN REWRITE_TAC[INT_ABS_NEG] THEN
     COND_CASES_TAC THEN REWRITE_TAC[INT_ABS_NEG] THEN
    (SUBGOAL_THEN `(&e:int) = &((e-1)+1)` SUBST1_TAC THENL [AP_TERM_TAC THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC IPOLY_ABS_BOUND THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `(lab:num->num) g IN 1..2*e*G` ASSUME_TAC THENL
      [MATCH_MP_TAC TSET_IN_RANGE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
     REPEAT CONJ_TAC THENL
      [ASM_INT_ARITH_TAC;
       UNDISCH_TAC `y IN ibox (2*e*G) (&2*P)` THEN
        REWRITE_TAC[ibox; IN_ELIM_THM; IN_NUMSEG] THEN STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
        [ASM_ARITH_TAC;
         MATCH_MP_TAC BLOCK_UB THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
       X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPECL [`hh:num->int`; `(lab:num->num) g`;
          `j:num`]) THEN ASM_SIMP_TAC[]]);
    ASM_SIMP_TAC[ISUM_CONST; FINITE_NUMSEG; CARD_NUMSEG] THEN
    REWRITE_TAC[ARITH_RULE `(G+1)-1 = G`] THEN INT_ARITH_TAC]);;

let rstx = new_definition
 `rstx (s:num->bool) (x:num->int) = (\i. if i IN s then x i else &0)`;;

let rbox = new_definition
 `rbox (s:num->bool) t (M:int) =
    {x:num->int | x IN ibox t M /\ (!i. ~(i IN s) ==> x i = &0)}`;;

let RSTX_IN_RBOX = prove
 (`!(s:num->bool) t (M:int) (x:num->int).
     &0 <= M /\ s SUBSET (1..t) /\ x IN ibox t M ==> rstx s x IN rbox s t M`,
  REPEAT GEN_TAC THEN REWRITE_TAC[rbox; ibox; rstx; IN_ELIM_THM] THEN
   STRIP_TAC THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  COND_CASES_TAC THEN ASM_SIMP_TAC[INT_ABS_NUM; INT_LE_REFL] THEN
  ASM_MESON_TAC[SUBSET]);;

let IMAGE_RSTX_IBOX = prove
 (`!(s:num->bool) t (M:int).
     &0 <= M /\ s SUBSET (1..t)
     ==> IMAGE (rstx s) (ibox t M) = rbox s t M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
   X_GEN_TAC `r:num->int` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:num->int` (CONJUNCTS_THEN2 SUBST1_TAC
    ASSUME_TAC)) THEN
    ASM_MESON_TAC[RSTX_IN_RBOX];
    DISCH_TAC THEN EXISTS_TAC `r:num->int` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rbox; IN_ELIM_THM]) THEN
      STRIP_TAC THEN
      REWRITE_TAC[rstx; FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
      COND_CASES_TAC THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[rbox; IN_ELIM_THM]) THEN
       SIMP_TAC[]]]);;

let glue = new_definition
 `glue (s:num->bool) t (r:num->int) (u:num->int) =
    (\i. if i IN s then r i else if i IN ((1..t) DIFF s) then u i else &0)`;;

let FIBER_EQ_IMAGE = prove
 (`!(s:num->bool) t (M:int) (r:num->int).
     &0 <= M /\ s SUBSET (1..t) /\ r IN rbox s t M
     ==> {x | x IN ibox t M /\ rstx s x = r} =
         IMAGE (glue s t r)
               {u | (!i. i IN ((1..t) DIFF s) ==> u i IN {v:int | abs v <= M})
                /\
                    (!i. ~(i IN ((1..t) DIFF s)) ==> u i = &0)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num->int` THEN
  RULE_ASSUM_TAC(REWRITE_RULE[rbox; ibox; IN_ELIM_THM]) THEN EQ_TAC THENL
   [STRIP_TAC THEN
    FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[rstx; FUN_EQ_THM]) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ibox; IN_ELIM_THM]) THEN
    EXISTS_TAC `rstx ((1..t) DIFF s) x` THEN
     REWRITE_TAC[rstx; glue; FUN_EQ_THM] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN TRY DISCH_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
     ASM_MESON_TAC[IN_DIFF; IN_NUMSEG];
    DISCH_THEN(X_CHOOSE_THEN `u:num->int` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[glue; rstx; ibox; IN_ELIM_THM; FUN_EQ_THM] THEN
    REPEAT CONJ_TAC THEN X_GEN_TAC `i:num` THEN TRY DISCH_TAC THEN
    REPEAT COND_CASES_TAC THEN ASM_REWRITE_TAC[INT_ABS_NUM; INT_LE_REFL] THEN
    ASM_MESON_TAC[IN_DIFF; IN_NUMSEG; SUBSET]]);;

let GLUE_INJ = prove
 (`!(s:num->bool) (t:num) (M:int) (r:num->int) (u:num->int) (u':num->int).
     (!i:num. ~(i IN ((1..t) DIFF s)) ==> u i = &0) /\
     (!i:num. ~(i IN ((1..t) DIFF s)) ==> u' i = &0) /\
     glue s t r u = glue s t r u'
     ==> u = u'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[glue; FUN_EQ_THM] THEN STRIP_TAC THEN
  X_GEN_TAC `i:num` THEN
  ASM_CASES_TAC `(i:num) IN ((1..t) DIFF s)` THENL
   [SUBGOAL_THEN `~((i:num) IN s)` ASSUME_TAC THENL
     [UNDISCH_TAC `(i:num) IN ((1..t) DIFF s)` THEN
      SIMP_TAC[IN_DIFF]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let FREEX_FIBER_SIZE = prove
 (`!(s:num->bool) t (M:int) (r:num->int).
     &0 <= M /\ s SUBSET (1..t) /\ r IN rbox s t M
     ==> CARD {x | x IN ibox t M /\ rstx s x = r} =
         (2 * num_of_int M + 1) EXP (CARD((1..t) DIFF s))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN ibox t M /\ rstx s x =
    r} HAS_SIZE (2 * num_of_int M + 1) EXP (CARD((1..t) DIFF s))`
   MP_TAC THENL
   [ALL_TAC; SIMP_TAC[HAS_SIZE]] THEN
  ASM_SIMP_TAC[FIBER_EQ_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:num->int`; `u':num->int`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL
     [`s:num->bool`;`t:num`;`M:int`;`r:num->int`;`u:num->int`;`u':num->int`]
      GLUE_INJ) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`&0:int`; `2 * num_of_int M + 1`; `{v:int | abs v <= M}`;
                   `CARD((1..t) DIFF s)`;
                     `(1..t) DIFF s`] HAS_SIZE_FUNSPACE) THEN
    ASM_SIMP_TAC[ABS_INT_HAS_SIZE] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[HAS_SIZE] THEN SIMP_TAC[FINITE_DIFF; FINITE_NUMSEG]]);;

let FIBER_G_EQ = prove
 (`!(t:num) (M:int) (s:num->bool) (G:(num->int)->num) (r:num->int).
     &0 <= M /\ s SUBSET (1..t) /\ (!x. G x = G (rstx s x)) /\ r IN rbox s t M
     ==> nsum {x | x IN ibox t M /\ rstx s x = r} G =
         (2 * num_of_int M + 1) EXP (CARD((1..t) DIFF s)) * G r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `nsum {x | x IN ibox t M /\ rstx s x = r} G =
    nsum {x | x IN ibox t M /\ rstx s x = r} (\x. G r)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `x:num->int` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:num->int` th)) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check(is_forall o concl)) THEN
  SUBGOAL_THEN `FINITE {x:num->int | x IN ibox t M /\
   rstx s x = r}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox t M` THEN
    REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CONST] THEN
  MP_TAC(ISPECL [`s:num->bool`; `t:num`; `M:int`;
    `r:num->int`] FREEX_FIBER_SIZE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MULT_SYM]);;

let FREE_X_SPLIT = prove
 (`!(t:num) (M:int) (s:num->bool) (G:(num->int)->num).
     &0 <= M /\ s SUBSET (1..t) /\ (!x. G x = G (rstx s x))
     ==> nsum (ibox t M) G =
         (2 * num_of_int M + 1) EXP (CARD((1..t) DIFF s)) *
         nsum (rbox s t M) G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`rstx s`; `G:(num->int)->num`;
    `ibox t M`] NSUM_IMAGE_GEN) THEN
  REWRITE_TAC[IBOX_FINITE] THEN
  ASM_SIMP_TAC[IMAGE_RSTX_IBOX] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `nsum (rbox s t M) (\y. nsum {x | x IN ibox t M /\ rstx s x = y} G) =
    nsum (rbox s t M) (\y. (2 * num_of_int M + 1) EXP (CARD((1..t) DIFF s)) * G
     y)`
   SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `r:num->int` THEN DISCH_TAC THEN
    BETA_TAC THEN
    MATCH_MP_TAC FIBER_G_EQ THEN REPEAT CONJ_TAC THEN
     FIRST_ASSUM MATCH_ACCEPT_TAC;
    REWRITE_TAC[NSUM_LMUL]]);;

let LVAL = new_definition
  `LVAL (bp:num->bool) (ss:num) =
   nsum {j | j < ss} (\j. if bp j then 2 EXP (ss-1-j) else 0)`;;

let LVAL_0 = prove
 (`!bp. LVAL bp 0 = 0`,
  GEN_TAC THEN REWRITE_TAC[LVAL] THEN
  SUBGOAL_THEN `{j | j < 0} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ARITH_TAC;
    REWRITE_TAC[NSUM_CLAUSES]]);;

let SETLT_SUC = prove
 (`!s. {j | j < SUC s} = 0 INSERT (IMAGE SUC {j | j < s})`,
  GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INSERT; IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `x:num` THEN EQ_TAC THEN STRIP_TAC THENL
   [ASM_CASES_TAC `x = 0` THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `x-1` THEN
    ASM_ARITH_TAC;
    ASM_ARITH_TAC; ASM_ARITH_TAC]);;

let LVAL_REC = prove
 (`!bp s. LVAL bp (SUC s) = (if bp 0 then 2 EXP s else 0) + LVAL (\j. bp(j+1))
  s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LVAL; SETLT_SUC] THEN
  SIMP_TAC[NSUM_CLAUSES; FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
  SUBGOAL_THEN `~(0 IN IMAGE SUC {j | j < s})` (fun th -> REWRITE_TAC[th])
   THENL
   [REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[NOT_SUC]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `SUC s - 1 - 0 = s`] THEN BINOP_TAC THENL
   [REFL_TAC; ALL_TAC] THEN
  W(fun (_,w) -> MP_TAC(ISPECL [`SUC`;
    `(\j. if bp j then 2 EXP (SUC s - 1 - j) else 0):num->num`;
      `{j | j < s}`] NSUM_IMAGE)) THEN
  ANTS_TAC THENL [MESON_TAC[SUC_INJ]; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `j:num` THEN
   REWRITE_TAC[IN_ELIM_THM; o_THM; ADD1] THEN
  DISCH_TAC THEN REWRITE_TAC[ARITH_RULE `SUC(j) = j + 1`] THEN AP_THM_TAC THEN
   AP_TERM_TAC THEN AP_TERM_TAC THEN ARITH_TAC);;

let LVAL_LT = prove
 (`!ss bp. LVAL bp ss < 2 EXP ss`,
  INDUCT_TAC THENL
   [REWRITE_TAC[LVAL_0; EXP; ARITH];
    GEN_TAC THEN REWRITE_TAC[LVAL_REC; EXP] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `\j. (bp:num->bool)(j+1)`) THEN
    COND_CASES_TAC THEN ASM_ARITH_TAC]);;

let RIFFLE_SHIFT = prove
 (`!t x d. 1 <= x /\ x + 2*d <= 2*t ==> RIFFLE t (x + 2*d) = RIFFLE t x + d`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[RIFFLE; IN_NUMSEG] THEN
  SUBGOAL_THEN `(1 <= x + 2*d /\ x + 2*d <= 2*t) /\ (1 <= x /\
   x <= 2*t)` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
  REWRITE_TAC[ODD_ADD; ODD_MULT; ARITH] THEN COND_CASES_TAC THEN
   ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let ARG_II = prove
 (`t = (2*B) * 2 EXP s /\ LVAL (\j. (bp:num->bool)(j+1)) s = V
    ==> (if bp 0 then t else 0) + 2 * B * V = 2 * (B * LVAL bp (SUC s))`,
  STRIP_TAC THEN REWRITE_TAC[LVAL_REC] THEN
  FIRST_ASSUM(fun th -> if concl th = `LVAL (\j. (bp:num->bool)(j+1)) s = V`
   then REWRITE_TAC[th] else NO_TAC) THEN
  SUBGOAL_THEN `(if bp 0 then t else 0) = (2*B) * (if bp 0 then 2 EXP s else
   0)` SUBST1_TAC THENL
   [COND_CASES_TAC THEN REWRITE_TAC[MULT_CLAUSES] THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_ADD_DISTRIB] THEN CONV_TAC NUM_RING);;

let LEAFIDX_BP_TRANS = prove
 (`!s bp B t i. t = B * 2 EXP s /\ 1 <= B /\ i IN 1..2*t
     ==> leafidx s t (\j:num. RIFFLE t) bp i = leafidx s t (\j:num. RIFFLE t)
      (\j. F) i + B * LVAL bp s`,
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    REWRITE_TAC[LEAFIDX; LVAL_0; MULT_CLAUSES; ADD_CLAUSES]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEAFIDX; CHQ] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REWRITE_TAC[ADD_CLAUSES] THEN
  ABBREV_TAC `Lb = leafidx s t (\j:num. RIFFLE t) (\j. bp(j+1)) i` THEN
  ABBREV_TAC `Lf = leafidx s t (\j:num. RIFFLE t) (\j. F) i` THEN
  SUBGOAL_THEN `t = (2*B) * 2 EXP s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Lb:num = Lf + (2*B) * LVAL (\j. bp(j+1)) s` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["Lb"; "Lf"] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`\j. (bp:num->bool)(j+1)`; `2*B:num`;
      `t:num`; `i:num`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `LVAL (\j. bp(j+1)) s < 2 EXP s` ASSUME_TAC THENL
   [REWRITE_TAC[LVAL_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `LVAL bp (SUC s) < 2 * 2 EXP s` ASSUME_TAC THENL
   [MP_TAC(SPECL [`SUC s`; `bp:num->bool`] LVAL_LT) THEN REWRITE_TAC[EXP] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `Lf IN BLK (2*B) t` MP_TAC THENL
   [EXPAND_TAC "Lf" THEN
    MP_TAC(SPECL [`s:num`; `t:num`; `2*B:num`] LEAFIDX_FF_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
     EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_BLK] THEN
  ABBREV_TAC `V = LVAL (\j. (bp:num->bool)(j+1)) s` THEN STRIP_TAC THENL
   [(* Lf in low part 1..2B *)
    SUBGOAL_THEN `(2*B) * V + 2 * B <= (2 * B) * 2 EXP s` ASSUME_TAC THENL
     [MATCH_MP_TAC(ARITH_RULE `(2*B)*V + 2*B <= (2*B)*(V+1) /\
      (2*B)*(V+1) <= (2*B)*2 EXP s ==> (2*B)*V + 2*B <= (2*B)*2 EXP s`) THEN
      CONJ_TAC THENL [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
       ARITH_TAC;
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC]; ALL_TAC] THEN
    SUBGOAL_THEN `Lb <= t /\ Lf <= t` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(if Lb <= t then Lb else Lb - t) = (if Lf <= t then Lf else
     Lf - t) + 2 * B * V` ASSUME_TAC THENL [ASM_SIMP_TAC[] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC ARG_II THEN (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[EXP] THEN ARITH_TAC; DISCH_TAC]) THEN
    SUBGOAL_THEN `(if Lb <= t then Lb else Lb - t) + (if bp 0 then t else 0) =
     (if Lf <= t then Lf else Lf - t) + 2 * (B * LVAL bp (SUC s))`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RIFFLE_SHIFT THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `2 * (B * LVAL bp (SUC s)) <= 2*t - 2*B` MP_TAC THENL
       [REWRITE_TAC[ARITH_RULE `2*(B*L) = (2*B)*L`] THEN
        SUBGOAL_THEN `2*t - 2*B = (2*B)*(2 * 2 EXP s - 1)` SUBST1_TAC THENL
         [REWRITE_TAC[LEFT_SUB_DISTRIB; MULT_CLAUSES] THEN
          ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_ARITH_TAC];
    SUBGOAL_THEN `~(Lf <= t) /\ ~(Lb <= t)` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(if Lb <= t then Lb else Lb - t) = (if Lf <= t then Lf else
     Lf - t) + 2 * B * V` ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC ARG_II THEN (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN
     REWRITE_TAC[EXP] THEN ARITH_TAC; DISCH_TAC]) THEN
    SUBGOAL_THEN `(if Lf <= t then Lf else Lf - t) = j` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `2 * (B * LVAL bp (SUC s)) + 2 * B <= 2 * t` ASSUME_TAC THENL
     [SUBGOAL_THEN `2 * (B * LVAL bp (SUC s)) + 2 * B = (2*B) * (LVAL bp (SUC
      s) + 1)` SUBST1_TAC THENL
       [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
        ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `2 * t = (2*B) * (2 * 2 EXP s)` SUBST1_TAC THENL
       [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [ASSUME `t = (2 * B) * 2 EXP
        s`] THEN ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(if Lb <= t then Lb else Lb - t) + (if bp 0 then t else 0) =
     (if Lf <= t then Lf else Lf - t) + 2 * (B * LVAL bp (SUC s))`
      SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC RIFFLE_SHIFT THEN CONJ_TAC THEN ASM_ARITH_TAC]);;

let CHSG_PRES = prove
 (`!s bp B t i. t = B * 2 EXP s /\ 1 <= B /\ i IN 1..2*t
     ==> (leafidx s t (\j:num. RIFFLE t) bp i <= t <=> leafidx s t (\j:num.
      RIFFLE t) (\j. F) i <= t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `leafidx s t (\j:num. RIFFLE t) (\j. F) i IN BLK B t`
   MP_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] LEAFIDX_FF_IMAGE))
    THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `i IN 1..2 * t` then MP_TAC th else
     NO_TAC) THEN
    FIRST_ASSUM(fun th -> if concl th = `t = B * 2 EXP s` then GEN_REWRITE_TAC
     (LAND_CONV o ONCE_DEPTH_CONV) [th] else NO_TAC) THEN
    REWRITE_TAC[MULT_ASSOC]; ALL_TAC] THEN
  MP_TAC(SPECL [`s:num`;`bp:num->bool`;`B:num`;`t:num`;`i:num`]
   LEAFIDX_BP_TRANS) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `B * LVAL bp s + B <= t` ASSUME_TAC THENL
   [SUBGOAL_THEN `B * LVAL bp s + B = B * (LVAL bp s + 1)` SUBST1_TAC THENL
     [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES]; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> if concl th = `t = B * 2 EXP s` then GEN_REWRITE_TAC
     RAND_CONV [th] else NO_TAC) THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
     MP_TAC(SPECL [`s:num`;`bp:num->bool`] LVAL_LT) THEN
      ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[IN_BLK] THEN STRIP_TAC THEN ASM_ARITH_TAC);;

let LEAFSG_BP_INV = prove
 (`!s bp B t i. t = B * 2 EXP s /\ 1 <= B /\ i IN 1..2*t
     ==> (leafsg s t (\j:num. RIFFLE t) bp i <=> leafsg s t (\j:num. RIFFLE t)
      (\j. F) i)`,
  INDUCT_TAC THENL [REWRITE_TAC[LEAFSG]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN REWRITE_TAC[LEAFSG] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `t = (2*B) * 2 EXP s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `leafsg s t (\j:num. RIFFLE t) (\j. bp(j+1)) i <=> leafsg s t
   (\j:num. RIFFLE t) (\j. F) i` SUBST1_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`\j. (bp:num->bool)(j+1)`; `2*B:num`;
     `t:num`; `i:num`]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `CHSG t (leafidx s t (\j:num. RIFFLE t) (\j. bp(j+1)) i) <=>
   CHSG t (leafidx s t (\j:num. RIFFLE t) (\j. F) i)` SUBST1_TAC THENL
   [REWRITE_TAC[CHSG] THEN AP_TERM_TAC THEN
    MP_TAC(SPECL [`s:num`;`\j. (bp:num->bool)(j+1)`; `2*B:num`; `t:num`;
      `i:num`] CHSG_PRES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let IBOX_PERM_MEM = prove
 (`!p n M hh. p permutes 1..n /\ hh IN ibox n M ==> (\i. hh(p i)) IN ibox n M`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[ibox; IN_ELIM_THM]) THEN
  REWRITE_TAC[ibox; IN_ELIM_THM] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   CONJ_TAC THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT1) THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[PERMUTES_IN_IMAGE];
    SUBGOAL_THEN `(p:num->num) i = i` SUBST1_TAC THENL
     [UNDISCH_TAC `p permutes 1..n` THEN REWRITE_TAC[permutes] THEN
      STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o CONJUNCT2) THEN DISCH_THEN MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[]]]);;

let IMAGE_IBOX_PERM = prove
 (`!p n M. p permutes 1..n ==> IMAGE (\hh:num->int. (\i. hh(p i))) (ibox n M) =
  ibox n M`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
   X_GEN_TAC `g:num->int` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `hh:num->int` (CONJUNCTS_THEN2 SUBST1_TAC
    ASSUME_TAC)) THEN
    MATCH_MP_TAC IBOX_PERM_MEM THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN EXISTS_TAC `(\i. g(inverse (p:num->num) i)):num->int` THEN
     CONJ_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      ASM_MESON_TAC[PERMUTES_INVERSES];
      MP_TAC(SPECL [`inverse(p:num->num)`;`n:num`;`M:int`;`g:num->int`]
       IBOX_PERM_MEM) THEN
      ASM_SIMP_TAC[PERMUTES_INVERSE]]]);;

let NSUM_IBOX_PERM = prove
 (`!p n M (Fn:(num->int)->num). p permutes 1..n
     ==> nsum (ibox n M) Fn = nsum (ibox n M) (\hh. Fn (\i. hh(p i)))`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC (LAND_CONV o RATOR_CONV o RAND_CONV) [SYM(SPEC `M:int`
   (MATCH_MP IMAGE_IBOX_PERM (ASSUME `p permutes 1..n`)))] THEN
  MP_TAC(ISPECL [`(\hh:num->int. (\i:num. hh((p:num->num)
   i))):(num->int)->(num->int)`; `Fn:(num->int)->num`;
     `ibox n M`] NSUM_IMAGE) THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num->int`;`b:num->int`] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `j:num` THEN
    SUBGOAL_THEN `(a:num->int)((p:num->num)(inverse p j)) =
     (b:num->int)(p(inverse p j))` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[FUN_EQ_THM]) THEN
      DISCH_THEN(MP_TAC o SPEC `inverse (p:num->num) j`) THEN REWRITE_TAC[];
      ASM_MESON_TAC[PERMUTES_INVERSES]];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF]]);;

let PERM_EXTEND = prove
 (`!(u:num->bool) (s:num->bool) (g:num->num).
    FINITE u /\ s SUBSET u /\ (IMAGE g s) SUBSET u /\
    (!x y. x IN s /\ y IN s /\ g x = g y ==> x = y)
    ==> ?p. p permutes u /\ (!x. x IN s ==> p x = g x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(s:num->bool) /\
   FINITE(IMAGE (g:num->num) s)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
    [ASM_MESON_TAC[FINITE_SUBSET]; MATCH_MP_TAC FINITE_IMAGE THEN
     ASM_MESON_TAC[FINITE_SUBSET]]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(u DIFF s) = CARD(u DIFF IMAGE (g:num->num) s)`
   ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF] THEN
    SUBGOAL_THEN `CARD(IMAGE (g:num->num) s) = CARD s` (fun th ->
     ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`u DIFF s:num->bool`;
    `u DIFF IMAGE (g:num->num) s`] CARD_EQ_BIJECTIONS) THEN
  ASM_SIMP_TAC[FINITE_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:num->num` (X_CHOOSE_THEN `hinv:num->num`
   STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x. if x IN s then (g:num->num) x else if x IN u then h x else x`
   THEN
  CONJ_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[PERMUTES_FINITE_INJECTIVE] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
    [ASM_MESON_TAC[SUBSET]; ASM_REWRITE_TAC[]];
    X_GEN_TAC `x:num` THEN DISCH_TAC THEN COND_CASES_TAC THENL
     [ASM_MESON_TAC[SUBSET; IN_IMAGE];
      SUBGOAL_THEN `(x:num) IN u DIFF s` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      FIRST_X_ASSUM(fun th -> if (let c=concl th in is_forall c && (try
       (is_conj(snd(dest_imp(snd(dest_forall c)))) ) with _ -> false)) then
        MP_TAC(SPEC `x:num` th) else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_DIFF; SUBSET]];
    MAP_EVERY X_GEN_TAC [`x:num`;`y:num`] THEN
     ASM_CASES_TAC `(x:num) IN u` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(y:num) IN u` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(x:num) IN s` THEN ASM_CASES_TAC `(y:num) IN s` THEN
     RULE_ASSUM_TAC(REWRITE_RULE[]) THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> let c = concl th in
      is_forall c && (try (let (a,_)=dest_imp(snd(strip_forall c)) in is_conj
       a) with _ -> false))) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      RULE_ASSUM_TAC(REWRITE_RULE[COND_CLAUSES]) THEN
      SUBGOAL_THEN `(y:num) IN u DIFF s` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      SUBGOAL_THEN `h(y:num) IN u DIFF IMAGE (g:num->num) s` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:num->num) x IN IMAGE g s` ASSUME_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(if x IN s then (g:num->num) x else h x) = (if y IN s then g
       y else h y)` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_DIFF];
      SUBGOAL_THEN `(x:num) IN u DIFF s` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      SUBGOAL_THEN `h(x:num) IN u DIFF IMAGE (g:num->num) s` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:num->num) y IN IMAGE g s` ASSUME_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(if x IN s then (g:num->num) x else h x) = (if y IN s then g
       y else h y)` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[IN_DIFF];
      SUBGOAL_THEN `(x:num) IN u DIFF s /\
       (y:num) IN u DIFF s` STRIP_ASSUME_TAC THENL
        [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      SUBGOAL_THEN `(hinv:num->num)((h:num->num) x) = x /\
       (hinv:num->num)((h:num->num) y) = y` STRIP_ASSUME_TAC THENL
        [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(if x IN s then (g:num->num) x else h x) = (if y IN s then g
       y else h y)` THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o AP_TERM `hinv:num->num`) THEN
         ASM_REWRITE_TAC[]]]);;

let TSET_SHIFT_IN_RANGE = prove
 (`!e G c t. 1 <= G /\ c + e <= e * G /\ t IN TSET e G ==> t + c IN 1..2*e*G`,
  REWRITE_TAC[TSET; IN_UNION; IN_IMAGE; IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
   ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

let SIGMA_EXISTS = prove
 (`!e G ss bp. 2 <= e /\ 1 <= G /\ G = 2 EXP ss
     ==> ?sigma. sigma permutes 1..2*e*G /\
                 (!t. t IN TSET e G ==> sigma t = t + e * LVAL bp ss)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`1..2*e*G`; `TSET e G`;
    `\t. t + e * LVAL bp ss`] PERM_EXTEND) THEN
  REWRITE_TAC[FINITE_NUMSEG] THEN ANTS_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC TSET_IN_RANGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `u:num` THEN
     DISCH_THEN(X_CHOOSE_THEN `t:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))
      THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       MATCH_MP_TAC TSET_SHIFT_IN_RANGE THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `e * LVAL bp ss + e = e * (LVAL bp ss + 1)`
         SUBST1_TAC THENL
          [REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES]; ALL_TAC] THEN
           ASM_REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
            MP_TAC(SPECL [`ss:num`;`bp:num->bool`] LVAL_LT) THEN ARITH_TAC;
    REPEAT GEN_TAC THEN ARITH_TAC]);;

let LEAF_SUMMAND_BP = prove
 (`!e (ss:num) (G:num) (bp:num->bool) (PSI:(num->int)->num->num->int)
  (hh:num->int) (sigma:num->num) (y:num->int).
     2 <= e /\ e-1 <= ss /\ 1 <= G /\ G = 2 EXP ss /\
     sigma permutes 1..2*e*G /\
     (!t. t IN TSET e G ==> sigma t = t + e * LVAL bp ss)
     ==> isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh i) (e-1)
      y) (e*G) (\j. RIFFLE(e*G)) bp hh i (y i)) =
         isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI (\l.
          hh(inverse sigma l)) (sigma i)) (e-1) y) (e*G) (\j. RIFFLE(e*G)) (\j.
           F) (\l. hh(sigma l)) i (y i))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[PLEAF_SGNRELAB; SGNRELAB] THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `leafidx ss (e*G) (\j:num. RIFFLE(e*G)) (\j. F) i IN TSET e G`
   ASSUME_TAC THENL
   [MATCH_MP_TAC LEAFIDX_INTO_TSET THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sigma (leafidx ss (e*G) (\j:num. RIFFLE(e*G)) (\j. F) i) =
   leafidx ss (e*G) (\j:num. RIFFLE(e*G)) bp i` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (let c = concl th in is_forall c && (try
    (rand(rand(snd(dest_imp(snd(dest_forall c))))) = `e * LVAL bp ss`) with _
     -> false)) then MP_TAC(SPEC `leafidx ss (e*G) (\j:num. RIFFLE(e*G)) (\j.
      F) i` th) else NO_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(SPECL [`ss:num`;`bp:num->bool`;`e:num`;`e*G:num`;`i:num`]
     LEAFIDX_BP_TRANS) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `2*e*G = 2*(e*G)`] THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `leafsg ss (e*G) (\j:num. RIFFLE(e*G)) bp i <=> leafsg ss (e*G)
   (\j:num. RIFFLE(e*G)) (\j. F) i` ASSUME_TAC THENL
   [MP_TAC(SPECL [`ss:num`;`bp:num->bool`;`e:num`;`e*G:num`;`i:num`]
    LEAFSG_BP_INV) THEN
    ASM_REWRITE_TAC[IN_NUMSEG; ARITH_RULE `2*e*G = 2*(e*G)`] THEN
     ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(\l. hh(sigma(inverse (sigma:num->num) l))):num->int = hh`
   SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `l:num` THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    AP_TERM_TAC THEN ASM_MESON_TAC[PERMUTES_INVERSES]; ALL_TAC] THEN
  REFL_TAC);;

let FIBERSUM_BP_INV = prove
 (`!e (ss:num) (G:num) (bp:num->bool) (P:int) (PSI:(num->int)->num->num->int)
  (sigma:num->num).
     2 <= e /\ e-1 <= ss /\ 1 <= G /\ G = 2 EXP ss /\
     sigma permutes 1..2*e*G /\
     (!t. t IN TSET e G ==> sigma t = t + e * LVAL bp ss)
     ==> nsum (ibox (2*e*G) (&2*P))
             (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh
                    i) (e-1) y) (e*G) (\j. RIFFLE(e*G)) bp hh i (y i)) = &0})
         = nsum (ibox (2*e*G) (&2*P))
             (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI
                    (\l. hh(inverse sigma l)) (sigma i)) (e-1) y) (e*G) (\j.
                     RIFFLE(e*G)) (\j. F) hh i (y i)) = &0})`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC RAND_CONV [MATCH_MP NSUM_IBOX_PERM (ASSUME `sigma permutes
   1..2*e*G`)] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `hh:num->int` THEN DISCH_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:num->int` THEN
  MATCH_MP_TAC(TAUT `(b <=> c) ==> (a /\ b <=> a /\ c)`) THEN
  MP_TAC(SPECL
   [`e:num`;`ss:num`;`G:num`;`bp:num->bool`;`PSI:(num->int)->num->num->int`;
     `hh:num->int`;`sigma:num->num`;`y:num->int`] LEAF_SUMMAND_BP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REFL_TAC);;

let LAB_INJ_LEMMA = prove
 (`!e (G:num) (lab:num->num).
     1 <= G /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> (!x y. x IN {g | g < 2*e} /\ y IN {g | g < 2*e} /\
      lab x = lab y ==> x = y)`,
  REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(lab:num->num) x` o check(fun th ->
   is_forall(concl th) && can (find_term (fun t -> t = `TSET e G`)) (concl th)
    && not(free_in `lab:num->num` (concl th) && can (find_term (fun t -> t =
     `lab g IN TSET e G`)) (concl th)))) THEN
  ANTS_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN
   ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`x:num`;`y:num`] o check(fun th -> let c=concl
   th in is_forall c && can (find_term (fun t -> t = `x':num`)) c)) THEN
    ASM_REWRITE_TAC[]);;

let IMAGE_LAB_EQ_TSET = prove
 (`!e (G:num) (lab:num->num).
     2 <= e /\ 1 <= G /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> IMAGE lab (0..2*e-1) = TSET e G`,
  REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `(0..2*e-1) = {g | g < 2*e}` SUBST1_TAC THENL
    [REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM] THEN
     ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `t:num` THEN
       EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:num` (CONJUNCTS_THEN2 SUBST1_TAC ASSUME_TAC))
    THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `t:num` o check(fun th -> is_forall(concl th)
      && can (find_term (fun u -> u = `TSET e G`)) (concl th) && not(can
       (find_term (fun u -> u = `lab g IN TSET e G`)) (concl th)))) THEN
        ASM_REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:num` STRIP_ASSUME_TAC o CONJUNCT1) THEN
     EXISTS_TAC `g:num` THEN ASM_REWRITE_TAC[]]);;

let CARD_IMAGE_LAB = prove
 (`!e (G:num) (lab:num->num).
     2 <= e /\ 1 <= G /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> CARD(IMAGE lab (0..2*e-1)) = 2*e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] IMAGE_LAB_EQ_TSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC TSET_CARD THEN ASM_REWRITE_TAC[]);;

let SUBSET_IMAGE_LAB = prove
 (`!e (G:num) (lab:num->num).
     2 <= e /\ 1 <= G /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> IMAGE lab (0..2*e-1) SUBSET 1..2*e*G`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] IMAGE_LAB_EQ_TSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC TSET_IN_RANGE THEN ASM_REWRITE_TAC[]);;

let CARD_DIFF_LAB = prove
 (`!e (G:num) (lab:num->num).
     2 <= e /\ 1 <= G /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> CARD((1..2*e*G) DIFF IMAGE lab (0..2*e-1)) = 2*e*G - 2*e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] SUBSET_IMAGE_LAB) THEN
   ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ASM_SIMP_TAC[CARD_DIFF; FINITE_NUMSEG] THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] CARD_IMAGE_LAB) THEN
   ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[CARD_NUMSEG_1]);;

let RHSWIDE_RSTX_INV = prove
 (`!e (G:num) (Cm0:int) (P:int) (cpsi:int) (lab:num->num) (hh:num->int).
     2 <= e
     ==> (\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi * (&2*P)
      pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                 (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                  (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0)) hh =
         (\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi * (&2*P)
          pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                 (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                  (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0)) (rstx
                   (IMAGE lab (0..2*e-1)) hh)`,
  REPEAT STRIP_TAC THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `zv:num->int` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `isum (0..2 * e - 1) (\g. rstx (IMAGE lab (0..2 * e - 1)) hh
   (lab g) * zv g) = isum (0..2 * e - 1) (\g. hh (lab g) * zv g)`
    SUBST1_TAC THENL [ALL_TAC; REFL_TAC] THEN
  MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `g:num` THEN REWRITE_TAC[IN_NUMSEG] THEN
   STRIP_TAC THEN REWRITE_TAC[rstx] THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SUBGOAL_THEN `(lab:num->num) g IN IMAGE lab (0..2 * e - 1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `g:num` THEN
    ASM_REWRITE_TAC[IN_NUMSEG]; ASM_REWRITE_TAC[]]);;

let ISUM_COUPLE = prove
 (`!e (lab:num->num) (hh:num->int) (hh':num->int) (v:num->int).
     2 <= e /\ (!i. i IN 1..2*e ==> hh' i = hh(lab(i-1)))
     ==> isum(1..2*e)(\i. hh' i * v(i-1)) = isum(0..2*e-1)(\g. hh(lab g) * v
      g)`,
  REPEAT STRIP_TAC THEN
   SUBGOAL_THEN `isum(1..2*e)(\i. hh' i * v(i-1)) = isum(1..2*e)(\i.
    (hh:num->int)((lab:num->num)(i-1)) * v(i-1))` SUBST1_TAC THENL
     [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_THM_TAC THEN AP_TERM_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`1`;
    `(\i. (hh:num->int)((lab:num->num)(i-1)) * v(i-1)):num->int`; `0`;
      `2*e-1`] ISUM_OFFSET) THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC[ARITH_RULE `0 + 1 = 1`; ARITH_RULE `i + 1 - 1 = i`] THEN
        SUBGOAL_THEN `(2*e-1)+1 = 2*e` SUBST1_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `(i + 1) - 1 = i`] THEN DISCH_THEN ACCEPT_TAC);;

let INNER_REINDEX = prove
 (`!e (lab:num->num) (G:num) (Cm0:int) (P:int) (WB:int)
    (hh:num->int) (hh':num->int).
     2 <= e /\ (!i. i IN 1..2*e ==> hh' i = hh(lab(i-1)))
     ==> nsum {zv | (!g. g < 2*e ==> abs(zv g) <= WB) /\
      (!g. ~(g < 2*e) ==> zv g = &0)}
                 (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                  (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0)
         = nsum {z | (!i. i IN 1..2*e ==> abs(z i) <= WB) /\
          (!i. ~(i IN 1..2*e) ==> z i = &0) /\
                     isum (1..2*e) (\i. hh' i * z i) = &0}
                 (\z. nproduct (1..2*e) (\i. num_of_int (Cm0 * P pow
                  (G-(e-1)))))`,
  REPEAT STRIP_TAC THEN
   SIMP_TAC[NPRODUCT_CONST; FINITE_NUMSEG; CARD_NUMSEG_1] THEN
    GEN_REWRITE_TAC (LAND_CONV) [GSYM NSUM_RESTRICT_SET] THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
   MAP_EVERY EXISTS_TAC [`\(zv:num->int). (\i. if i IN 1..2*e then zv(i-1) else
    &0):num->int`;
      `\(z:num->int). (\g. if g < 2*e then z(g+1) else &0):num->int`] THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN CONJ_TAC THENL
   [X_GEN_TAC `z:num->int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `g:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th ->
       if concl th =
          `!i. i IN 1..2 * e ==> abs ((z:num->int) i) <= WB`
       then MATCH_MP_TAC th else NO_TAC) THEN REWRITE_TAC[IN_NUMSEG] THEN
        ASM_ARITH_TAC;
      X_GEN_TAC `g:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `isum (0..2 * e - 1) (\g. hh (lab g) * (if g < 2 * e then z
       (g + 1) else &0)) = isum (0..2 * e - 1) (\g.
        (hh:num->int)((lab:num->num) g) * (\g. z(g+1)) g)` SUBST1_TAC THENL
         [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `g:num` THEN
          REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
           CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
            SUBGOAL_THEN `g < 2 * e` (fun th -> REWRITE_TAC[th]) THEN
             ASM_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(SPECL [`e:num`; `lab:num->num`; `hh:num->int`; `hh':num->int`;
        `(\g. z(g+1)):num->int`] ISUM_COUPLE) THEN ASM_REWRITE_TAC[] THEN
         DISCH_THEN(SUBST1_TAC o SYM) THEN
          SUBGOAL_THEN `isum (1..2 * e) (\i. hh' i * z (i - 1 + 1)) = isum
           (1..2 * e) (\i. hh' i * z i)` SUBST1_TAC THENL
            [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
             REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
              CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN AP_TERM_TAC THEN
               AP_TERM_TAC THEN ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THENL
        [RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
         SUBGOAL_THEN `i - 1 < 2 * e` (fun th -> REWRITE_TAC[th]) THENL
          [ASM_ARITH_TAC; AP_TERM_TAC THEN
           ASM_ARITH_TAC];
             FIRST_X_ASSUM(fun th ->
              if concl th =
                 `!i. ~(i IN 1..2 * e) ==> (z:num->int) i = &0`
              then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
               ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
    X_GEN_TAC `zv:num->int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th ->
       if concl th =
          `!g. g < 2 * e ==> abs ((zv:num->int) g) <= WB`
       then MATCH_MP_TAC th else NO_TAC) THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `isum (1..2 * e) (\i. hh' i * (if i IN 1..2 * e then zv (i -
       1) else &0)) = isum (1..2*e)(\i. hh' i * zv(i-1))` SUBST1_TAC THENL
        [MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
         CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
          ASM_REWRITE_TAC[]; ALL_TAC] THEN
           MP_TAC(SPECL [`e:num`; `lab:num->num`; `hh:num->int`;
             `hh':num->int`; `zv:num->int`] ISUM_COUPLE) THEN
            ASM_REWRITE_TAC[] THEN
              DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `g:num` THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THENL
        [SUBGOAL_THEN `g + 1 IN 1..2 * e` (fun th -> REWRITE_TAC[th]) THENL
         [REWRITE_TAC[IN_NUMSEG] THEN
          ASM_ARITH_TAC; REWRITE_TAC[ARITH_RULE `(g+1)-1 = g`]];
            FIRST_X_ASSUM(fun th ->
             if concl th =
                `!g. ~(g < 2 * e) ==> (zv:num->int) g = &0`
             then MP_TAC(SPEC `g:num` th) else NO_TAC) THEN
              ASM_REWRITE_TAC[] THEN MESON_TAC[]]]]);;

let LABINV_EXISTS = prove
 (`!e (G:num) (lab:num->num).
     2 <= e /\ 1 <= G /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> ?labinv. (!t. t IN IMAGE lab (0..2*e-1) ==> labinv t IN (0..2*e-1) /\
      lab(labinv t) = t) /\
                  (!g. g IN (0..2*e-1) ==> labinv(lab g) = g)`,
  REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`lab:num->num`; `0..2*e-1`;
     `IMAGE (lab:num->num) (0..2*e-1)`] BIJECTIVE_ON_LEFT_RIGHT_INVERSE) THEN
      ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(!x y. x IN 0..2 * e - 1 /\ y IN 0..2 * e - 1 /\
   lab x = lab y ==> x = y) /\
    (!y. y IN IMAGE (lab:num->num) (0..2 * e - 1) ==> (?x. x IN 0..2 * e - 1 /\
     lab x = y))` ASSUME_TAC THENL
   [CONJ_TAC THENL
    [MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] LAB_INJ_LEMMA) THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_NUMSEG; IN_ELIM_THM] THEN
      DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`x:num`;`y:num`] THEN STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_ARITH_TAC; REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]];
    ASM_MESON_TAC[]]);;

let OUTER_REINDEX = prove
 (`!e (G:num) (Cm0:int) (P:int) (cpsi:int) (lab:num->num).
     2 <= e /\ 1 <= G /\ &1 <= P /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t)
     ==> nsum (rbox (IMAGE lab (0..2*e-1)) (2*e*G) (&2*P))
             (\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi *
              (&2*P) pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                     (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                      (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0))
         = nsum {hh | (!i. i IN 1..2*e ==> abs(hh i) <= (&2*P)) /\
          (!i. ~(i IN 1..2*e) ==> hh i = &0)}
                 (\hh. nsum {z | (!i. i IN 1..2*e ==> abs(z i) <= (&G) * &e *
                  cpsi * (&2 * P) pow (e-1)) /\
                   (!i. ~(i IN 1..2*e) ==> z i = &0) /\
                                 isum (1..2*e) (\i. hh i * z i) = &0}
                            (\z. nproduct (1..2*e) (\i. num_of_int (Cm0 * P pow
                             (G-(e-1))))))`,
  REPEAT STRIP_TAC THEN
   MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] LABINV_EXISTS) THEN
    ASM_REWRITE_TAC[] THEN
     DISCH_THEN(X_CHOOSE_THEN `labinv:num->num` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC NSUM_EQ_GENERAL_INVERSES THEN
   MAP_EVERY EXISTS_TAC [`\(hh:num->int). (\i. if i IN 1..2*e then hh(lab(i-1))
    else &0):num->int`;
      `\(hh:num->int). (\l. if l IN IMAGE lab (0..2*e-1) then hh(labinv l + 1)
       else &0):num->int`] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
        CONJ_TAC THENL
   [X_GEN_TAC `y:num->int` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[rbox; ibox; IN_ELIM_THM] THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN REPEAT CONJ_TAC THEN
       X_GEN_TAC `l:num` THEN DISCH_TAC THENL
       [COND_CASES_TAC THENL [ALL_TAC; REWRITE_TAC[INT_ABS_NUM] THEN
        ASM_INT_ARITH_TAC] THEN
        SUBGOAL_THEN `(labinv:num->num) l IN (0..2*e-1)` MP_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN REWRITE_TAC[IN_NUMSEG] THEN
          STRIP_TAC THEN
           FIRST_X_ASSUM(fun th ->
            if concl th =
               `!i. i IN 1..2 * e ==> abs ((y:num->int) i) <= &2 * P`
            then MATCH_MP_TAC th else NO_TAC) THEN
             REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        SUBGOAL_THEN `~((l:num) IN IMAGE (lab:num->num) (0..2*e-1))` (fun th ->
         REWRITE_TAC[th]) THEN
          MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] SUBSET_IMAGE_LAB) THEN
           ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `i:num` THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THENL
        [ALL_TAC;
          FIRST_X_ASSUM(fun th ->
           if concl th =
              `!i. ~(i IN 1..2 * e) ==> (y:num->int) i = &0`
           then MP_TAC(SPEC `i:num` th) else NO_TAC) THEN
            ASM_REWRITE_TAC[] THEN MESON_TAC[]] THEN
      SUBGOAL_THEN `(i-1) IN (0..2*e-1)` ASSUME_TAC THENL
       [REWRITE_TAC[IN_NUMSEG] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
         ASM_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(lab:num->num)(i-1) IN IMAGE (lab:num->num) (0..2*e-1)`
           (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_IMAGE] THEN
            EXISTS_TAC `i-1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
             SUBGOAL_THEN `(labinv:num->num)((lab:num->num)(i-1)) = i - 1`
              SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN
               ASM_REWRITE_TAC[]; ALL_TAC] THEN AP_TERM_TAC THEN
                RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC];
    X_GEN_TAC `x:num->int` THEN REWRITE_TAC[rbox; ibox; IN_ELIM_THM] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THENL
     [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(fun th ->
       if concl th =
          `!i. i IN 1..2 * e * G ==> abs ((x:num->int) i) <= &2 * P`
       then MATCH_MP_TAC th else NO_TAC) THEN
        MATCH_MP_TAC TSET_IN_RANGE THEN ASM_REWRITE_TAC[] THEN
         FIRST_X_ASSUM(fun th -> if concl th = `!g. g < 2 * e ==> lab g IN TSET
          e G` then MATCH_MP_TAC th else NO_TAC) THEN
           RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FUN_EQ_THM] THEN X_GEN_TAC `l:num` THEN
       CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN COND_CASES_TAC THENL
       [SUBGOAL_THEN `(labinv:num->num) l IN (0..2*e-1) /\
        (lab:num->num)(labinv l) = l` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
          RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN
           SUBGOAL_THEN `(labinv:num->num) l + 1 IN 1..2*e` (fun th ->
            REWRITE_TAC[th]) THENL [REWRITE_TAC[IN_NUMSEG] THEN
             ASM_ARITH_TAC; ALL_TAC] THEN
              REWRITE_TAC[ARITH_RULE `((labinv:num->num) l + 1) - 1 = labinv
               l`] THEN ASM_REWRITE_TAC[];
        CONV_TAC SYM_CONV THEN ASM_MESON_TAC[]];
      CONV_TAC SYM_CONV THEN
       MP_TAC(SPECL [`e:num`; `lab:num->num`; `G:num`; `Cm0:int`; `P:int`;
         `(&G:int) * &e * cpsi * (&2 * P) pow (e-1)`; `x:num->int`;
           `(\i. if i IN 1..2*e then (x:num->int)((lab:num->num)(i-1)) else
            &0):num->int`] INNER_REINDEX) THEN
             CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ANTS_TAC THENL
              [SIMP_TAC[]; DISCH_THEN SUBST1_TAC THEN REFL_TAC] THEN
               ASM_REWRITE_TAC[]]]);;

let LEAF_PARTA_EQ = prove
 (`!e (G:num) (Cm0:int) (P:int) (cpsi:int) (lab:num->num) (Bn:num).
     2 <= e /\ 1 <= G /\ &1 <= P /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
     (&2*(&2*P)+ &1) pow (2*e*G - 2*e) *
             &(nsum {hh | (!i. i IN 1..(2*e) ==> abs(hh i) <= (&2*P)) /\
              (!i. ~(i IN 1..(2*e)) ==> hh i = &0)}
                  (\hh. nsum {z | (!i. i IN 1..(2*e) ==> abs(z i) <= (&G) * &e
                   * cpsi * (&2 * P) pow (e-1)) /\
                    (!i. ~(i IN 1..(2*e)) ==> z i = &0) /\
                                  isum (1..(2*e)) (\i. hh i * z i) = &0}
                             (\z. nproduct (1..(2*e)) (\i. num_of_int (Cm0 * P
                              pow (G-(e-1))))))) = &Bn
     ==> nsum (ibox (2*e*G) (&2*P))
             (\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi *
              (&2*P) pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                     (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                      (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0)) =
                       Bn`,
  REPEAT STRIP_TAC THEN
   MP_TAC(ISPECL [`2*e*G`; `&2*P:int`; `IMAGE (lab:num->num) (0..2*e-1)`;
     `(\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi * (&2*P)
      pow (e-1)) /\
       (!g. ~(g < 2*e) ==> zv g = &0)} (\zv. if isum(0..2*e-1)(\g. hh(lab g) *
        zv g) = &0 then (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else
         0)):(num->int)->num`] FREE_X_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THENL
   [ASM_INT_ARITH_TAC; MATCH_MP_TAC SUBSET_IMAGE_LAB THEN
    ASM_REWRITE_TAC[]; GEN_TAC THEN MATCH_MP_TAC RHSWIDE_RSTX_INV THEN
     ASM_REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
   MP_TAC(SPECL [`e:num`;`G:num`;`lab:num->num`] CARD_DIFF_LAB) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
     MP_TAC(SPECL [`e:num`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;`lab:num->num`]
      OUTER_REINDEX) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check(fun th -> can (find_term (fun t -> t =
   `&Bn:int`)) (concl th))) THEN
  SUBGOAL_THEN
   `&2 * (&2 * P) + &1 = &(2 * num_of_int(&2 * P) + 1):int`
   SUBST1_TAC THENL
   [SUBGOAL_THEN `&(num_of_int(&2 * P)):int = &2 * P` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD; GSYM INT_OF_NUM_MUL] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    REWRITE_TAC[INT_OF_NUM_POW; INT_OF_NUM_MUL; INT_OF_NUM_EQ] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC]);;

let MAXMULT_ARITH_BND = prove
 (`!(B:int) (P:int) (e:num) (k:num) (G:num) (Cm0:int).
     &1 <= B /\ &1 <= P /\ e-1 <= k /\ k <= G /\
     B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0
     ==> B * (&2 * (&2 * P) + &1) pow (G-k) * (&2 * P) pow (k-(e-1))
         <= Cm0 * P pow (G-(e-1))`,
  REPEAT STRIP_TAC THEN EXPAND_TAC "Cm0" THEN
  SUBGOAL_THEN
   `&2 * (&2 * (P:int)) + &1 <= &5 * P`
   ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * (&2 * (P:int)) + &1) pow (G-k) <= (&5 * P) pow (G-k)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE2 THEN CONJ_TAC THENL
    [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `(B:int) * (&5 * P) pow (G-k) * (&2 * P) pow (k-(e-1))` THEN
   CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
    [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[INT_POW_MUL] THEN
  MATCH_MP_TAC INT_EQ_IMP_LE THEN
  SUBGOAL_THEN
   `(P:int) pow (G-k) * P pow (k-(e-1)) = P pow (G-(e-1))`
   MP_TAC THENL
   [REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  CONV_TAC INT_RING);;

let PSI_FLAT_FOLD_REDUCTION_LR = prove
 (`!e (G:num) (P:int) (PSI:(num->int)->num->num->int) (s:num)
  (pp:num->num->num) (B:num).
    1 <= e * G /\ (!j. pp j permutes 1..(2*e*G)) /\
    (!bp:num->bool. nsum (ibox (2*e*G) (&2*P))
       (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
             isum(1..(2*e*G))(\i. pleaf s (\hh i y. hh i * ipoly (PSI hh i)
              (e-1) y) (e*G) pp bp hh i (y i)) = &0}) <= B)
    ==> nsum (ibox (2*e*G) (&2*P))
          (\hh. CARD {y:num->int | y IN ibox (2*e*G) (&2*P) /\
               isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) = &0})
                <= B`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e*G:num`; `&2*P:int`; `ibox (2*e*G) (&2*P)`] PGEN_TOWER) THEN
  ASM_REWRITE_TAC[IBOX_FINITE] THEN
  DISCH_THEN(MP_TAC o SPECL [`s:num`;
    `(\hh (i:num) (y:int). hh i * ipoly (PSI hh i) (e-1)
     y):(num->int)->num->int->int`; `pp:num->num->num`; `B:num`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  SIMP_TAC[LE_MULT_LCANCEL; EXP_EQ_0; ARITH_EQ]);;

let WACL_LEAF_BOUND_FROM_FLAT = prove
 (`!e (G:num) (P:int) (PSI:(num->int)->num->num->int) (Bn:num).
     1 <= e * G /\
     nsum (ibox (2*e*G) (&2*P))
       (\hh. CARD {y:num->int | y IN ibox (2*e*G) (&2*P) /\
             isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) = &0})
              <= Bn
     ==> ?(s:num) (pp:num->num->num).
            1 <= e * G /\ (!j. pp j permutes 1..(2*e*G)) /\
            (!bp:num->bool. nsum (ibox (2*e*G) (&2*P))
               (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                     isum(1..(2*e*G))(\i. pleaf s (\hh i y. hh i * ipoly (PSI
                      hh i) (e-1) y) (e*G) pp bp hh i (y i)) = &0}) <= Bn)`,
  REPEAT STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`0`; `(\(j:num) (x:num). x):num->num->num`] THEN
  REWRITE_TAC[PLEAF] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM I_DEF; PERMUTES_I];
    ASM_REWRITE_TAC[]]);;

let FLAT_FROM_LEAF_RIFFLE = prove
 (`!e k (c:int) (G:num) (Cm0:int) (P:int) (cpsi:int) (L:int)
  (PSI:(num->int)->num->num->int) (Bn:num) (ss:num).
      2 <= e /\ k <= G /\ e-1 <= G /\ 1 <= G /\ &1 <= P /\ G = 2 EXP ss /\
      (!bp:num->bool. nsum (ibox (2*e*G) (&2*P))
          (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh i)
                 (e-1) y) (e*G) (\j. RIFFLE(e*G)) bp hh i (y i)) = &0}) <= Bn)
      ==> nsum (ibox (2*e*G) (&2*P))
            (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                  isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) =
                   &0}) <= Bn`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC PSI_FLAT_FOLD_REDUCTION_LR THEN
  MAP_EVERY EXISTS_TAC [`ss:num`; `(\j:num. RIFFLE(e*G)):num->num->num`] THEN
  SUBGOAL_THEN `1 <= e * G` ASSUME_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n=0)`; MULT_EQ_0] THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    GEN_TAC THEN REWRITE_TAC[ARITH_RULE `2*e*G = 2*(e*G)`] THEN
     MATCH_ACCEPT_TAC RIFFLE_PERMUTES;
    FIRST_ASSUM ACCEPT_TAC]);;

let GROUPED_TO_TARGET_ARITH_WIDE = prove
 (`!e (G:num) (P:int) (Cm0:int) (Cf:int) (W:int) (MaxMult:num) (GN:num)
  (FS:num).
     2 <= e /\ e-1 <= G /\ &1 <= P /\ &1 <= Cm0 /\ &1 <= Cf /\ &1 <= W /\
     &MaxMult <= Cm0 * P pow (G-(e-1)) /\
     &GN <= &(MaxMult EXP (2*e)) * Cf * ((&2 * P) * &2 * (W * (&2 * P) pow
      (e-1))) pow (2*e-1) /\
     &FS <= (&2*(&2*P)+ &1) pow (2*e*G - 2*e) * &GN
     ==> &FS <= (&5 pow (G-1) * Cm0) pow (2*e) * (P pow (G-(e-1))) pow (2*e) *
      P pow (2*e*G - 2*e) *
                (Cf * ((&2 * P) * &2 * W * (&2 * P) pow (e-1)) pow (2*e-1))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `fam:int = ((&2 * P) * &2 * W * (&2 * P) pow (e-1)) pow (2*e-1)` THEN
  SUBGOAL_THEN `&0 <= (P:int)` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (P:int) pow (e-1) /\
   &0 <= P pow (G-(e-1))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC INT_POW_LE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&2 * (P:int)) * &2 * W * (&2 * P) pow (e-1)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
         [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE THEN
          ASM_INT_ARITH_TAC]]]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (fam:int)` ASSUME_TAC THENL
   [EXPAND_TAC "fam" THEN MATCH_MP_TAC INT_POW_LE THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (Cf:int)` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&2*(&2*(P:int))+ &1) pow (2*e*G-2*e) <=
   &5 pow (2*e*G-2*e) * P pow
   (2*e*G-2*e)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_POW_MUL] THEN MATCH_MP_TAC INT_POW_LE2 THEN
    ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `&(MaxMult EXP (2*e)):int <=
    (Cm0 * P pow (G-(e-1))) pow (2*e)`
   ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_POW] THEN MATCH_MP_TAC INT_POW_LE2 THEN
    ASM_REWRITE_TAC[INT_POS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&GN:int) <= (Cm0 * P pow (G-(e-1))) pow (2*e) * Cf * fam`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `(&(MaxMult EXP (2*e)):int) * Cf * fam` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[INT_ARITH `a * Cf * fam = a * (Cf * fam):int`] THEN
    MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INT_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `((&5:int) pow (2*e*G-2*e) * P pow (2*e*G-2*e)) * ((Cm0 * P pow
   (G-(e-1))) pow (2*e) * Cf * fam)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC
     `(&2*(&2*(P:int))+ &1) pow (2*e*G-2*e) * &GN` THEN
     ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_POS] THEN
    MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[INT_POW_MUL] THEN
    SUBGOAL_THEN `(&5:int) pow (2*e*G-2*e) =
                  (&5 pow (G-1)) pow (2*e)`
     SUBST1_TAC THENL
     [REWRITE_TAC[INT_POW_POW] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `?q. G = q + 1` (CHOOSE_THEN SUBST_ALL_TAC) THENL
       [EXISTS_TAC `G-1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[ARITH_RULE `(q+1)-1 = q`;
        ARITH_RULE `2*e*(q+1) - 2*e = 2*e*q`] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_EQ_IMP_LE THEN CONV_TAC INT_RING]);;

let BBOX_LOWER = prove
 (`!e (G:num) (cpsi:int) (P:int).
     2 <= e /\ 1 <= G /\ &1 <= cpsi /\ &1 <= P
     ==> &2 * P <= &G * &e * cpsi * (&2 * P) pow (e-1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= (&G:int) * &e * cpsi` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_ONE_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC INT_ONE_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (P:int) <= (&2 * P) pow (e-1)`
   ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM INT_POW_1] THEN
    MATCH_MP_TAC INT_POW_MONO THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `(&2 * (P:int)) pow (e-1)` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(&G:int) * &e * cpsi * (&2 * P) pow (e-1) =
    (&G * &e * cpsi) * (&2 * P) pow (e-1)`
   SUBST1_TAC THENL
   [CONV_TAC INT_RING; ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM(INT_ARITH `&1 * x = x:int`)] THEN
  MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[]; MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC]);;

let SMALLP_CORE_BND = prove
 (`!e (G:num) (P:int) (cpsi:int) (PSI:(num->int)->num->num->int).
      2 <= e /\ 1 <= G /\ &1 <= P /\ &1 <= cpsi /\
      ~(&2 * (&G * &e * cpsi * (&2 * P) pow (e-1)) <= (&2 * P) pow (2*e-1))
      ==> &(nsum (ibox (2*e*G) (&2 * P))
             (\hh. CARD {y:num->int | y IN ibox (2*e*G) (&2 * P) /\
                  isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) =
                   &0}))
          <= (&4 * &G * &e * cpsi) pow (4*e*G)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `NB = CARD(ibox (2*e*G) (&2 * P))` THEN
  SUBGOAL_THEN `nsum (ibox (2*e*G) (&2 * P))
             (\hh. CARD {y:num->int | y IN ibox (2*e*G) (&2 * P) /\
                  isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) =
                   &0}) <= NB * NB` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `nsum (ibox (2*e*G) (&2 * P)) (\hh:num->int. NB)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LE THEN REWRITE_TAC[IBOX_FINITE] THEN
      X_GEN_TAC `hh:num->int` THEN DISCH_TAC THEN EXPAND_TAC "NB" THEN
      MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[];
      ASM_SIMP_TAC[NSUM_CONST; IBOX_FINITE] THEN EXPAND_TAC "NB" THEN
       REWRITE_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&2 * (P:int)) pow e < &2 * &G * &e * cpsi`
   ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check(fun th -> is_neg(concl th))) THEN
    REWRITE_TAC[INT_NOT_LE] THEN
    SUBGOAL_THEN
     `(&2 * (P:int)) pow (2*e-1) =
      (&2 * P) pow (e-1) * (&2 * P) pow e`
     SUBST1_TAC THENL
     [REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN
      ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (&2 * (P:int)) pow (e-1)` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_POW_LT THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(&2 * (P:int)) pow (e-1) * (&2 * P) pow e <
     (&2 * P) pow (e-1) *
     (&2 * &G * &e * cpsi)` MP_TAC THENL
     [MATCH_MP_TAC INT_LTE_TRANS THEN
      EXISTS_TAC
       `(&2:int) * &G * &e * cpsi * (&2 * P) pow (e - 1)` THEN
      CONJ_TAC THENL [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_EQ_IMP_LE THEN
       CONV_TAC INT_RING]; ALL_TAC] THEN
    ASM_SIMP_TAC[INT_LT_LMUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 * (P:int) <= (&2 * P) pow e` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [GSYM INT_POW_1] THEN
    MATCH_MP_TAC INT_POW_MONO THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ASM_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `&2 * (&2 * (P:int)) + &1 <= &4 * &G * &e * cpsi`
   ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(&NB:int) <= (&4 * &G * &e * cpsi) pow (2*e*G)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `(&2 * (&2 * (P:int)) + &1) pow (2*e*G)` THEN
    CONJ_TAC THENL
     [EXPAND_TAC "NB" THEN MATCH_MP_TAC CARD_IBOX_BND THEN ASM_INT_ARITH_TAC;
      MATCH_MP_TAC INT_POW_LE2 THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (&4 * &G * &e * (cpsi:int)) pow (2*e*G)`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE THEN
    REPEAT(MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC]) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&(NB * NB):int` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN
  SUBGOAL_THEN
   `(&4 * &G * &e * (cpsi:int)) pow (4*e*G) =
    (&4 * &G * &e * cpsi) pow (2*e*G) *
    (&4 * &G * &e * cpsi) pow (2*e*G)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_POW_ADD] THEN AP_TERM_TAC THEN
    ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_MUL2 THEN ASM_REWRITE_TAC[INT_OF_NUM_LE; INT_POS] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[]);;

let DPWIH2 = new_definition
 `DPWIH2 e <=>
    ?k. e <= k /\
        !(A:int). &1 <= A
          ==> ?B. &1 <= B /\
              !(ffam:num->num->int) P m.
                  &1 <= P /\
                  (!j. j IN 1..k ==> ~(ffam j e = &0)) /\
                  (!j j'. j IN 1..k /\
                   j' IN 1..k ==> abs(ffam j e) = abs(ffam j' e)) /\
                  (!j i. j IN 1..k /\
                   i <= e ==> abs(ffam j i) <= A * P pow (e - i))
                  ==> &(CARD {x | x IN ibox k P /\
                                  isum(1..k)(\j. ipoly (ffam j) e (x j)) = m})
                      <= B * P pow (k - e)`;;

let MCOUNT_UNIFORM_W = prove
 (`!d. DPWIH2 d
    ==> ?k. d <= k /\
        !(A:int). &1 <= A ==> ?B. &1 <= B /\
        !(ffam:num->num->int) M a. &1 <= M /\
            (!j. j IN 1..k ==> ~(ffam j d = &0)) /\
            (!j j'. j IN 1..k /\
             j' IN 1..k ==> abs(ffam j d) = abs(ffam j' d)) /\
            (!j i. j IN 1..k /\ i <= d ==> abs(ffam j i) <= A * M pow (d - i))
            ==> &(amcount (\j. ipoly (ffam j) d) k M a) <= B * M pow (k - d)`,
  GEN_TAC THEN REWRITE_TAC[DPWIH2] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A:int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:int` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`ffam:num->num->int`; `M:int`; `a:int`] THEN
   STRIP_TAC THEN
  REWRITE_TAC[amcount] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`ffam:num->num->int`;`M:int`;`a:int`]) THEN
   ASM_REWRITE_TAC[]);;

let GROUP_MULT_GEN_DP_W = prove
 (`!d. 1 <= d /\ DPWIH2 d
    ==> ?k. d <= k /\
        !(A:int). &1 <= A ==> ?B. &1 <= B /\
        !(ffam:num->num->int) G M z. k <= G /\ &1 <= M /\
            (!j. j IN 1..k ==> ~(ffam j d = &0)) /\
            (!j j'. j IN 1..k /\
             j' IN 1..k ==> abs(ffam j d) = abs(ffam j' d)) /\
            (!j i. j IN 1..k /\ i <= d ==> abs(ffam j i) <= A * M pow (d - i))
            ==> &(CARD {w | w IN ibox G M /\
             isum(1..G)(\j. ipoly (ffam j) d (w j)) = z})
                <= B * (&2 * M + &1) pow (G - k) * M pow (k - d)`,
  GEN_TAC THEN STRIP_TAC THEN
   FIRST_ASSUM(MP_TAC o MATCH_MP MCOUNT_UNIFORM_W) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A:int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:int` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`ffam:num->num->int`; `G:num`; `M:int`; `z:int`] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`1 <= d:num`; `d <= k:num`] THEN
    ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (B:int) * M pow (k-d)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
    [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE THEN
     ASM_INT_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `c0 = num_of_int(B * M pow (k-d))` THEN
  SUBGOAL_THEN `(&c0:int) = B * M pow (k-d)` ASSUME_TAC THENL
   [EXPAND_TAC "c0" THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\j. ipoly ((ffam:num->num->int) j) d`; `k:num`; `G:num`;
    `M:int`; `z:int`; `c0:num`] MCOUNT_SPLIT_DP) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [X_GEN_TAC `a:int` THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`ffam:num->num->int`;`M:int`;`a:int`]) THEN
    ASM_REWRITE_TAC[amcount] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `&(CARD (ibox (G-k) M) * c0):int` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `&(CARD(ibox (G-k) M)):int <= (&2 * M + &1) pow (G-k)`
   MP_TAC THENL
   [MP_TAC(ISPECL [`G-k:num`;`M:int`] CARD_IBOX_BND) THEN ANTS_TAC THENL
    [ASM_INT_ARITH_TAC; REWRITE_TAC[]]; ALL_TAC] THEN
  DISCH_TAC THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `(&2 * (M:int) + &1) pow (G-k) * (B * M pow (k-d))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC INT_LE_RMUL THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC INT_EQ_IMP_LE THEN REWRITE_TAC[INT_MUL_AC]]);;

let SIGNED_GROUP_MULT_W = prove
 (`!d. 1 <= d /\ DPWIH2 d
    ==> ?k. d <= k /\
        !(A:int). &1 <= A ==> ?B. &1 <= B /\
        !(psi:num->int) (neg:num->bool) G M z. k <= G /\ &1 <= M /\
            ~(psi d = &0) /\
            (!i. i <= d ==> abs(psi i) <= A * M pow (d - i))
            ==> &(CARD {w | w IN ibox G M /\
                    isum(1..G)(\j. if neg j then --(ipoly psi d (w j)) else
                     ipoly psi d (w j)) = z})
                <= B * (&2 * M + &1) pow (G - k) * M pow (k - d)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP GROUP_MULT_GEN_DP_W (CONJ (ASSUME `1 <= d`) (ASSUME `DPWIH2
   d`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try fst(dest_var(fst(dest_forall(concl th))))="A"
   with _ -> false)
                          then MP_TAC(SPEC `A:int` th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `B:int` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`psi:num->int`; `neg:num->bool`; `G:num`; `M:int`;
    `z:int`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`sgnf (\j:num. (psi:num->int)) neg`; `G:num`;
    `M:int`; `z:int`] o
    check(fun th -> is_forall(concl th) && (try
     fst(dest_var(fst(dest_forall(concl th))))="ffam" with _ -> false))) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
      X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`\j:num. (psi:num->int)`; `neg:num->bool`; `j:num`;
        `d:num`] SGNF_LEAD) THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`j:num`;`j':num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\j:num. (psi:num->int)`; `neg:num->bool`; `j:num`;
        `d:num`] SGNF_ABS) THEN
      MP_TAC(ISPECL [`\j:num. (psi:num->int)`; `neg:num->bool`; `j':num`;
        `d:num`] SGNF_ABS) THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       REPEAT(DISCH_THEN SUBST1_TAC) THEN REFL_TAC;
      MAP_EVERY X_GEN_TAC [`j:num`;`i:num`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`\j:num. (psi:num->int)`; `neg:num->bool`; `j:num`;
        `i:num`] SGNF_ABS) THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
     AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `w:num->int` THEN
    MATCH_MP_TAC(TAUT `(b<=>c) ==> (a/\b<=>a/\c)`) THEN AP_THM_TAC THEN
     AP_TERM_TAC THEN
    MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\j:num. (psi:num->int)`; `neg:num->bool`; `j:num`; `d:num`;
      `(w:num->int) j`] SGNF_IPOLY) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[]]);;

let PER_GROUP_MULT_BND_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int)
     (psi:num->int) (neg:num->bool) (z:int).
      e-1 <= k /\ &1 <= B /\ &1 <= cpsi /\ k <= G /\ &1 <= P /\
      B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
      ~(psi (e-1) = &0) /\
       (!i. i <= e-1 ==> abs(psi i) <= cpsi * (&2 * P) pow (e-1-i)) /\
      (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (zz:int). k <= GG /\
       &1 <= M /\ ~(psi (e-1) = &0) /\
          (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
          ==> &(CARD {w | w IN ibox GG M /\
           isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
            (e-1) (w j)) = zz})
              <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1)))
      ==> CARD {w | w IN ibox G (&2 * P) /\
                    isum(1..G)(\j. if neg j then --ipoly psi (e-1) (w j) else
                     ipoly psi (e-1) (w j)) = z}
          <= num_of_int(Cm0 * P pow (G-(e-1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= (&5:int) pow (G-k)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&2:int) pow (k-(e-1))` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (Cm0:int)` ASSUME_TAC THENL
   [EXPAND_TAC "Cm0" THEN MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_LE_MUL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 <= (Cm0:int) * P pow (G-(e-1))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE THEN
      ASM_INT_ARITH_TAC]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  SUBGOAL_THEN
   `&(num_of_int(Cm0 * P pow (G-(e-1)))):int =
    Cm0 * P pow (G-(e-1))`
   SUBST1_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC
   `(B:int) * (&2 * (&2 * P) + &1) pow (G-k) *
    (&2 * P) pow (k-(e-1))` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL [`psi:num->int`; `neg:num->bool`; `G:num`;
     `&2 * P:int`; `z:int`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[];
    MATCH_MP_TAC MAXMULT_ARITH_BND THEN ASM_REWRITE_TAC[]]);;

let PER_GROUP_WBND_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int) (hh:num->int) (lab:num->num)
   (en:num->num->num) ss.
     2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ 1 <= G /\ &1 <= P /\
      &1 <= cpsi /\
     &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
     (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
     (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
      &1 <= M /\ ~(psi (e-1) = &0) /\
         (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
         ==> &(CARD {w | w IN ibox GG M /\
          isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
           (e-1) (w j)) = z})
             <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
     (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) /\ j <= (e-1)
          ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
     (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
     (!g. g < 2*e ==> lab g IN TSET e G)
     ==> !g v. g < 2*e
         ==> CARD {u | u IN ibox G (&2*P) /\
          isum(1..G)(\i. if leafsg ss (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g
           (i-1)) then --ipoly (PSI hh (lab g)) (e-1) (u i) else ipoly (PSI hh
            (lab g)) (e-1) (u i)) = v}
             <= num_of_int (Cm0 * P pow (G-(e-1)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(lab:num->num) g IN 1..2*e*G` ASSUME_TAC THENL
   [MATCH_MP_TAC TSET_IN_RANGE THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(SPECL [`e:num`;`k:num`;`B:int`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;
    `PSI (hh:num->int) ((lab:num->num) g):num->int`;
    `\i:num. leafsg ss (e*G) (\j. RIFFLE(e*G)) (\j. F) ((en:num->num->num) g
     (i-1))`;
    `v:int`] PER_GROUP_MULT_BND_W) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`hh:num->int`;
       `(lab:num->num) g`] o check(fun th -> let c =
        concl th in is_forall c && (try (fst(dest_var(fst(dest_forall
         c)))="hh") with _ -> false) && can (find_term (fun t -> t =
          `(e:num)-1`)) c && (try
           is_neg(snd(strip_forall(snd(dest_imp(snd(strip_forall c)))))) with _
            -> false))) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`hh:num->int`; `(lab:num->num) g`;
        `i:num`] o check(fun th -> let c =
         concl th in is_forall c && (try (fst(dest_var(fst(dest_forall
          c)))="hh") with _ -> false) && can (find_term (fun t -> t =
           `cpsi:int`)) c)) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN ACCEPT_TAC]);;

let LEAF_PERHH_WBND_W = prove
 (`!e k (B:int) ss (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int) (hh:num->int) (lab:num->num)
   (en:num->num->num).
     2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= ss /\ 1 <= G /\
      &1 <= P /\ &1 <= cpsi /\
     G = 2 EXP ss /\
     &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
     (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
     (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
      &1 <= M /\ ~(psi (e-1) = &0) /\
         (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
         ==> &(CARD {w | w IN ibox GG M /\
          isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
           (e-1) (w j)) = z})
             <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
     (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) /\ j <= (e-1)
          ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
     (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
     (!g r. g < 2*e /\ r < G ==> en g r IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g r) = lab g) /\
     (!g i. g < 2*e /\ i IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g ==> ?!r. r < G /\
       en g r = i)
     ==> CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh
                    i) (e-1) y) (e*G) (\j. RIFFLE(e*G)) (\j. F) hh i (y i)) =
                     &0}
         <= nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi * (&2*P)
          pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                 (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                  (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL
   [`e:num`;`ss:num`;`G:num`;`P:int`;`PSI:(num->int)->num->num->int`;
     `hh:num->int`;`lab:num->num`;`en:num->num->num`] LEAF_COUNT_RESHAPE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  FIRST_ASSUM(fun th -> if concl th = `G = 2 EXP ss` then REWRITE_TAC[SYM th]
   else NO_TAC) THEN
  MP_TAC(ISPECL [`e:num`; `G:num`; `&2*P:int`;
    `\(g:num) (i:num) (x:int). if leafsg ss (e*G) (\j. RIFFLE(e*G)) (\j. F)
     ((en:num->num->num) g (i-1)) then --(ipoly (PSI (hh:num->int)
      ((lab:num->num) g)) (e-1) x) else ipoly (PSI hh (lab g)) (e-1) x`;
        `\g:num. (hh:num->int)((lab:num->num) g)`;
          `num_of_int (Cm0 * P pow (G-(e-1)))`;
            `{zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi * (&2*P) pow
             (e-1)) /\
              (!g. ~(g < 2*e) ==> (zv:num->int) g = &0)}`] PERHH_MBLOCK_BND)
               THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
   REWRITE_TAC[ARITH_RULE `(2*e)*G = 2*e*G`] THEN
  ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[FINITE_GBOX];
    MP_TAC(SPECL
     [`e:num`;`k:num`;`B:int`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;
       `PSI:(num->int)->num->num->int`;`hh:num->int`;`lab:num->num`;
         `en:num->num->num`;`ss:num`] PER_GROUP_WBND_W) THEN ASM_REWRITE_TAC[];
    MP_TAC(SPECL
     [`e:num`;`ss:num`;`G:num`;`P:int`;`cpsi:int`;
       `PSI:(num->int)->num->num->int`;`hh:num->int`;`lab:num->num`;
         `en:num->num->num`] BLOCK_IN_WBOX) THEN ASM_REWRITE_TAC[]]);;

let LEAF_SUMMED_WBND_W = prove
 (`!e k (B:int) ss (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int) (lab:num->num) (en:num->num->num).
     2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= ss /\ 1 <= G /\
      &1 <= P /\ &1 <= cpsi /\
     G = 2 EXP ss /\
     &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
     (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
     (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
      &1 <= M /\ ~(psi (e-1) = &0) /\
         (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
         ==> &(CARD {w | w IN ibox GG M /\
          isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
           (e-1) (w j)) = z})
             <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
     (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
      i IN 1..(2*e*G) /\ j <= (e-1)
          ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
     (!g. g < 2*e ==> lab g IN TSET e G) /\
     (!t. t IN TSET e G ==> ?!g. g < 2*e /\ lab g = t) /\
     (!g r. g < 2*e /\ r < G ==> en g r IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) (en g r) = lab g) /\
     (!g i. g < 2*e /\ i IN 1..2*e*G /\
      leafidx ss (e*G) (\j. RIFFLE(e*G)) (\j. F) i = lab g ==> ?!r. r < G /\
       en g r = i)
     ==> nsum (ibox (2*e*G) (&2*P))
             (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh
                    i) (e-1) y) (e*G) (\j. RIFFLE(e*G)) (\j. F) hh i (y i)) =
                     &0})
         <= nsum (ibox (2*e*G) (&2*P))
             (\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi *
              (&2*P) pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                     (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                      (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else 0))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_LE THEN REWRITE_TAC[IBOX_FINITE] THEN
  X_GEN_TAC `hh:num->int` THEN DISCH_TAC THEN
   CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  MATCH_MP_TAC LEAF_PERHH_WBND_W THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `B:int`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if concl th = `G = 2 EXP ss` then REWRITE_TAC[SYM th]
   else NO_TAC) THEN
  EXISTS_TAC `en:num->num->num` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ibox; IN_ELIM_THM]) THEN
  FIRST_ASSUM(fun th -> if concl th = `G = 2 EXP ss` then REWRITE_TAC[SYM th]
   else NO_TAC) THEN
  ASM_REWRITE_TAC[]);;

let LEAF_RIFFLE_GROUPED_BND_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int) (Bn:num) (ss:num).
      2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= G /\ 1 <= G /\
       &1 <= P /\ &1 <= cpsi /\
      e-1 <= ss /\
      G = 2 EXP ss /\
      &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
      (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
      (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
       &1 <= M /\ ~(psi (e-1) = &0) /\
          (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
          ==> &(CARD {w | w IN ibox GG M /\
           isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
            (e-1) (w j)) = z})
              <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
      (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) /\ j <= (e-1)
           ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
      (&2*(&2*P)+ &1) pow (2*e*G - 2*e) *
             &(nsum {hh | (!i. i IN 1..(2*e) ==> abs(hh i) <= (&2*P)) /\
              (!i. ~(i IN 1..(2*e)) ==> hh i = &0)}
                  (\hh. nsum {z | (!i. i IN 1..(2*e) ==> abs(z i) <= (&G) * &e
                   * cpsi * (&2 * P) pow (e-1)) /\
                    (!i. ~(i IN 1..(2*e)) ==> z i = &0) /\
                                  isum (1..(2*e)) (\i. hh i * z i) = &0}
                             (\z. nproduct (1..(2*e)) (\i. num_of_int (Cm0 * P
                              pow (G-(e-1))))))) = &Bn
      ==> (!bp:num->bool. nsum (ibox (2*e*G) (&2*P))
             (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                   isum(1..(2*e*G))(\i. pleaf ss (\hh i y. hh i * ipoly (PSI hh
                    i) (e-1) y) (e*G) (\j. RIFFLE(e*G)) bp hh i (y i)) = &0})
                     <= Bn)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`ss:num`;`bp:num->bool`] SIGMA_EXISTS) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `sigma:num->num` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL
   [`e:num`;`ss:num`;`G:num`;`bp:num->bool`;`P:int`;
     `PSI:(num->int)->num->num->int`;`sigma:num->num`] FIBERSUM_BP_INV) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC]) THEN
  MP_TAC(SPECL [`e:num`;`ss:num`;`G:num`] LEAF_BLOCK_REINDEX_SK) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC]) THEN
  DISCH_THEN(X_CHOOSE_THEN `lab:num->num` (X_CHOOSE_THEN `en:num->num->num`
   STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `nsum (ibox (2*e*G) (&2*P))
             (\hh. nsum {zv | (!g. g < 2*e ==> abs(zv g) <= &G * &e * cpsi *
              (&2*P) pow (e-1)) /\ (!g. ~(g < 2*e) ==> zv g = &0)}
                     (\zv. if isum(0..2*e-1)(\g. hh(lab g) * zv g) = &0 then
                      (num_of_int (Cm0 * P pow (G-(e-1)))) EXP (2*e) else
                       0))` THEN
  CONJ_TAC THENL
   [MP_TAC(SPECL
    [`e:num`;`k:num`;`B:int`;`ss:num`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;
       `(\(hh:num->int) (i:num). PSI (\l:num. hh(inverse (sigma:num->num) l))
        (sigma i)):(num->int)->num->num->int`;
       `lab:num->num`;`en:num->num->num`] LEAF_SUMMED_WBND_W) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    (ANTS_TAC THENL [ALL_TAC; DISCH_THEN ACCEPT_TAC]) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM(ASSUME `G = 2 EXP ss`)] THEN
     CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`hh:num->int`; `i:num`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       length(fst(strip_forall(concl th)))=2 && (try
        is_neg(snd(dest_imp(snd(strip_forall(concl th))))) with _ -> false)
         then MATCH_MP_TAC th else NO_TAC) THEN
      CONJ_TAC THENL
       [X_GEN_TAC `l:num` THEN DISCH_TAC THEN BETA_TAC THEN
        FIRST_X_ASSUM(fun th -> if concl th = `!l. l IN 1..2*e*G ==>
         abs((hh:num->int) l) <= &2 * P` then MATCH_MP_TAC th else NO_TAC) THEN
        ASM_MESON_TAC[PERMUTES_INVERSE; PERMUTES_IN_IMAGE];
        ASM_MESON_TAC[PERMUTES_IN_IMAGE]];
      REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
       length(fst(strip_forall(concl th)))=3 && can (find_term (fun t -> t =
        `cpsi:int`)) (concl th) then MATCH_MP_TAC th else NO_TAC) THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `l:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th -> if concl th = `!l. l IN 1..2*e*G ==>
         abs((hh:num->int) l) <= &2 * P` then MATCH_MP_TAC th else NO_TAC) THEN
        ASM_MESON_TAC[PERMUTES_INVERSE; PERMUTES_IN_IMAGE];
        ASM_MESON_TAC[PERMUTES_IN_IMAGE]]];
    MP_TAC(SPECL
     [`e:num`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;`lab:num->num`;`Bn:num`]
      LEAF_PARTA_EQ) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC THEN
     REWRITE_TAC[LE_REFL]]]);;

let FLAT_LEAF_BND_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int) (Bn:num).
      2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= G /\ 1 <= G /\
       &1 <= P /\ &1 <= cpsi /\
      (?ss. e-1 <= ss /\ G = 2 EXP ss) /\
      &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
      (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
      (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
       &1 <= M /\ ~(psi (e-1) = &0) /\
          (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
          ==> &(CARD {w | w IN ibox GG M /\
           isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
            (e-1) (w j)) = z})
              <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
      (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) /\ j <= (e-1)
           ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
      (&2*(&2*P)+ &1) pow (2*e*G - 2*e) *
             &(nsum {hh | (!i. i IN 1..(2*e) ==> abs(hh i) <= (&2*P)) /\
              (!i. ~(i IN 1..(2*e)) ==> hh i = &0)}
                  (\hh. nsum {z | (!i. i IN 1..(2*e) ==> abs(z i) <= (&G) * &e
                   * cpsi * (&2 * P) pow (e-1)) /\
                    (!i. ~(i IN 1..(2*e)) ==> z i = &0) /\
                                  isum (1..(2*e)) (\i. hh i * z i) = &0}
                             (\z. nproduct (1..(2*e)) (\i. num_of_int (Cm0 * P
                              pow (G-(e-1))))))) = &Bn
      ==> nsum (ibox (2*e*G) (&2*P))
            (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                  isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) =
                   &0}) <= Bn`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL
   [`e:num`;`k:num`;`B:int`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;`&1:int`;
     `PSI:(num->int)->num->num->int`;`Bn:num`;
       `ss:num`] FLAT_FROM_LEAF_RIFFLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  MP_TAC(SPECL
   [`e:num`;`k:num`;`B:int`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;
     `PSI:(num->int)->num->num->int`;`Bn:num`;
       `ss:num`] LEAF_RIFFLE_GROUPED_BND_W) THEN
  ASM_REWRITE_TAC[]);;

let WACL_LEAF_BOUND_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int) (Bn:num).
      2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= G /\ 1 <= G /\
       &1 <= P /\ &1 <= cpsi /\
      (?ss. e-1 <= ss /\ G = 2 EXP ss) /\
      &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
      (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
      (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
       &1 <= M /\ ~(psi (e-1) = &0) /\
          (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
          ==> &(CARD {w | w IN ibox GG M /\
           isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
            (e-1) (w j)) = z})
              <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
      (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) /\ j <= (e-1)
           ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
      (&2*(&2*P)+ &1) pow (2*e*G - 2*e) *
             &(nsum {hh | (!i. i IN 1..(2*e) ==> abs(hh i) <= (&2*P)) /\
              (!i. ~(i IN 1..(2*e)) ==> hh i = &0)}
                  (\hh. nsum {z | (!i. i IN 1..(2*e) ==> abs(z i) <= (&G) * &e
                   * cpsi * (&2 * P) pow (e-1)) /\
                    (!i. ~(i IN 1..(2*e)) ==> z i = &0) /\
                                  isum (1..(2*e)) (\i. hh i * z i) = &0}
                             (\z. nproduct (1..(2*e)) (\i. num_of_int (Cm0 * P
                              pow (G-(e-1))))))) = &Bn
      ==> ?(s:num) (pp:num->num->num).
             1 <= e * G /\ (!j. pp j permutes 1..(2*e*G)) /\
             (!bp:num->bool. nsum (ibox (2*e*G) (&2*P))
                (\hh. CARD {y | y IN ibox (2*e*G) (&2*P) /\
                      isum(1..(2*e*G))(\i. pleaf s (\hh i y. hh i * ipoly (PSI
                       hh i) (e-1) y) (e*G) pp bp hh i (y i)) = &0}) <= Bn)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC WACL_LEAF_BOUND_FROM_FLAT THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n=0)`; MULT_EQ_0] THEN ASM_ARITH_TAC;
    MP_TAC(SPECL
     [`e:num`;`k:num`;`B:int`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;
       `PSI:(num->int)->num->num->int`;`Bn:num`] FLAT_LEAF_BND_W) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXISTS_TAC `ss:num` THEN
     ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]]);;

let PSI_LEAF_REGROUP_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int)
  (PSI:(num->int)->num->num->int).
      2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= G /\ 1 <= G /\
       &1 <= P /\ &1 <= cpsi /\
      (?ss. e-1 <= ss /\ G = 2 EXP ss) /\
      &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
      (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
       &1 <= M /\ ~(psi (e-1) = &0) /\
          (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
          ==> &(CARD {w | w IN ibox GG M /\
           isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
            (e-1) (w j)) = z})
              <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
      (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
      (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) /\ j <= (e-1)
           ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j))
      ==> ?(mult:num->int->num) (MaxMult:num).
      &MaxMult <= Cm0 * P pow (G-(e-1)) /\
      (!i z. mult i z <= MaxMult) /\
      &(nsum (ibox (2 * e * G) (&2 * P))
             (\hh. CARD {y:num->int | y IN ibox (2 * e * G) (&2 * P) /\
                  isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e - 1) (y i)) =
                   &0}))
       <= (&2*(&2*P)+ &1) pow (2*e*G - 2*e) *
             &(nsum {hh | (!i. i IN 1..(2*e) ==> abs(hh i) <= (&2*P)) /\
              (!i. ~(i IN 1..(2*e)) ==> hh i = &0)}
                  (\hh. nsum {z | (!i. i IN 1..(2*e) ==> abs(z i) <= &G * &e *
                   cpsi * (&2 * P) pow (e-1)) /\
                    (!i. ~(i IN 1..(2*e)) ==> z i = &0) /\
                                  isum (1..(2*e)) (\i. hh i * z i) = &0}
                             (\z. nproduct (1..(2*e)) (\i. mult i (z i)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `G:num` with _ -> false)
                          then ASSUME_TAC(EXISTS(`?ss:num. e-1 <= ss /\
                           G = 2 EXP ss`,`ss:num`) (CONJ (ASSUME `e-1 <= ss`)
                            th)) else NO_TAC) THEN
  EXISTS_TAC `\(i:num) (z:int). num_of_int(Cm0 * P pow (G-(e-1)))` THEN
  EXISTS_TAC `num_of_int(Cm0 * P pow (G-(e-1)))` THEN
  SUBGOAL_THEN `&0 <= (Cm0:int) * P pow (G-(e-1))` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE THEN
      ASM_INT_ARITH_TAC]; ALL_TAC] THEN
  SUBGOAL_THEN `&(num_of_int(Cm0 * P pow (G-(e-1)))) = Cm0 * P pow (G-(e-1))`
   ASSUME_TAC THENL
   [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INT_LE_REFL; LE_REFL] THEN
  ABBREV_TAC `RHS:int = (&2 * &2 * P + &1) pow (2 * e * G - 2 * e) *
    &(nsum
      {hh | (!i. i IN 1..2 * e ==> abs (hh i) <= &2 * P) /\
            (!i. ~(i IN 1..2 * e) ==> hh i = &0)}
     (\hh.
          nsum
          {z | (!i. i IN 1..2 * e ==> abs (z i) <= &G * &e * cpsi * (&2 * P)
           pow (e - 1)) /\
               (!i. ~(i IN 1..2 * e) ==> z i = &0) /\
               isum (1..2 * e) (\i. hh i * z i) = &0}
          (\z. nproduct (1..2 * e) (\i. num_of_int (Cm0 * P pow (G - (e -
           1)))))))` THEN
  SUBGOAL_THEN `&0 <= (RHS:int)` ASSUME_TAC THENL
   [EXPAND_TAC "RHS" THEN MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC; REWRITE_TAC[INT_POS]];
    ALL_TAC] THEN
  ABBREV_TAC `Bn = num_of_int RHS` THEN
  SUBGOAL_THEN `&Bn:int = RHS` ASSUME_TAC THENL
   [EXPAND_TAC "Bn" THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `&Bn:int` with _ -> false)
   then SUBST1_TAC(SYM th) else NO_TAC) THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN
  MATCH_MP_TAC PSI_FLAT_FOLD_REDUCTION_LR THEN
  MATCH_MP_TAC WACL_LEAF_BOUND_W THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `B:int`; `Cm0:int`; `cpsi:int`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(fun th -> if (try rhs(concl th) = `Bn:num` with _ -> false)
   then SUBST1_TAC(SYM th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
   ASM_REWRITE_TAC[]);;

let WIDE_CORE_BND_W = prove
 (`!e k (B:int) (G:num) (Cm0:int) (P:int) (cpsi:int) (Cfp:int) (Cf:int)
  (PSI:(num->int)->num->num->int).
      2 <= e /\ e-1 <= k /\ &1 <= B /\ k <= G /\ e-1 <= G /\ 1 <= G /\
       &1 <= P /\ &1 <= cpsi /\
      (?ss. e-1 <= ss /\ G = 2 EXP ss) /\
      &1 <= Cm0 /\ B * &5 pow (G-k) * &2 pow (k-(e-1)) = Cm0 /\
      &1 <= Cfp /\ Cf <= Cfp /\
      &1 <= &G * &e * cpsi /\
      (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG /\
       &1 <= M /\ ~(psi (e-1) = &0) /\
          (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
          ==> &(CARD {w | w IN ibox GG M /\
           isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else ipoly psi
            (e-1) (w j)) = z})
              <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1))) /\
      (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
      (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2 * P) /\
       i IN 1..(2*e*G) /\ j <= (e-1)
           ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) - j)) /\
      (!A B' mfn. &1 <= A /\ A <= &2 * B' /\
       &2 * B' <= A pow (CARD (1..2 * e) - 1)
          ==> isum {a | (!i. i IN 1..2 * e ==> abs (a i) <= A) /\
           (!i. ~(i IN 1..2 * e) ==> a i = &0)}
                   (\a. &(lincount (1..2 * e) a (mfn a) B')) <= Cf * (A * &2 *
                    B') pow (CARD (1..2 * e) - 1)) /\
      &2 * (&G * &e * cpsi * (&2 * P) pow (e-1)) <= (&2 * P) pow (2*e-1)
      ==> &(nsum (ibox (2*e*G) (&2 * P))
             (\hh. CARD {y:num->int | y IN ibox (2*e*G) (&2 * P) /\
                  isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) =
                   &0}))
          <= ((&5 pow (G-1) * Cm0) pow (2*e) * (Cfp * (&G * &e * cpsi) pow
           (2*e-1)) * (&2 pow (e+1)) pow (2*e-1)) * P pow (2*(2*e*G) - e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `G:num` with _ -> false)
                          then ASSUME_TAC(EXISTS(`?ss:num. e-1 <= ss /\
                           G = 2 EXP ss`,`ss:num`) (CONJ (ASSUME `e-1 <= ss`)
                            th)) else NO_TAC) THEN
  MP_TAC(SPECL
   [`e:num`;`k:num`;`B:int`;`G:num`;`Cm0:int`;`P:int`;`cpsi:int`;
     `PSI:(num->int)->num->num->int`] PSI_LEAF_REGROUP_W) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mult:num->int->num` (X_CHOOSE_THEN `MaxMult:num`
   STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[ARITH_RULE `2*2*e*G-e = 2*(2*e*G)-e`] THEN
  MATCH_MP_TAC DP_RED_TO_CLOSE_WIDE THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    ASM_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC INT_ONE_LE_MUL THEN ASM_REWRITE_TAC[] THEN
     MATCH_MP_TAC INT_POW_LE_1 THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC GROUPED_TO_TARGET_ARITH_WIDE THEN
  EXISTS_TAC `MaxMult:num` THEN
  EXISTS_TAC `nsum
  {hh | (!i. i IN 1..2 * e ==> abs (hh i) <= &2 * P) /\
        (!i. ~(i IN 1..2 * e) ==> hh i = &0)}
 (\hh.
      nsum
      {z | (!i.
                i IN 1..2 * e
                ==> abs (z i) <= &G * &e * cpsi * (&2 * P) pow (e - 1)) /\
           (!i. ~(i IN 1..2 * e) ==> z i = &0) /\
           isum (1..2 * e) (\i. hh i * z i) = &0}
      (\z. nproduct (1..2 * e) (\i:num. mult i (z i))))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(&2 * (P:int)) * &2 * (&G * &e * cpsi) * (&2 * P) pow (e - 1) = (&2 *
   P) * &2 * (&G * &e * cpsi * (&2 * P) pow (e-1))` SUBST1_TAC THENL
   [CONV_TAC INT_RING; ALL_TAC] THEN
  MATCH_MP_TAC GN_UNIF_BND_GEN THEN
  EXISTS_TAC `Cf:int` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`e:num`;`G:num`;`cpsi:int`;`P:int`] BBOX_LOWER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= &G * &e * (cpsi:int) * (&2 * P) pow (e - 1)` MP_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_POS];
      MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
       [REWRITE_TAC[INT_POS];
        MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
         [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC]]];
    ALL_TAC] THEN
  INT_ARITH_TAC);;

let WARING_PSI_FIBER_TOWER_W = prove
 (`!e k (G:num). 2 <= e /\ e-1 <= k /\ k <= G /\ e-1 <= G /\ 1 <= G /\
      (?ss. e-1 <= ss /\ G = 2 EXP ss)
    ==> !cpsi:int. &1 <= cpsi
        ==> !B:int. &1 <= B /\
            (!(psi:num->int) (neg:num->bool) (GG:num) (M:int) (z:int). k <= GG
             /\ &1 <= M /\ ~(psi (e-1) = &0) /\
                (!i. i <= e-1 ==> abs(psi i) <= cpsi * M pow (e-1-i))
                ==> &(CARD {w | w IN ibox GG M /\
                 isum(1..GG)(\j. if neg j then --ipoly psi (e-1) (w j) else
                  ipoly psi (e-1) (w j)) = z})
                    <= B * (&2 * M + &1) pow (GG-k) * M pow (k-(e-1)))
            ==> ?cc:int. &1 <= cc /\
                !(PSI:(num->int)->num->num->int) (P:int). &1 <= P /\
                    (!(hh:num->int) i. (!l. l IN 1..(2*e*G) ==> abs(hh l) <= &2
                     * P) /\ i IN 1..(2*e*G) ==> ~(PSI hh i (e-1) = &0)) /\
                    (!(hh:num->int) i j. (!l. l IN 1..(2*e*G) ==> abs(hh l) <=
                     &2 * P) /\ i IN 1..(2*e*G) /\ j <= (e-1)
                         ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) -
                          j))
                    ==> &(nsum (ibox (2*e*G) (&2 * P))
                           (\hh. CARD {y:num->int | y IN ibox (2*e*G) (&2 * P)
                            /\
                                isum(1..(2*e*G))(\i. hh i * ipoly (PSI hh i)
                                 (e-1) (y i)) = &0}))
                        <= cc * P pow (2*(2*e*G) - e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try lhs(concl th) = `G:num` with _ -> false)
                          then ASSUME_TAC(EXISTS(`?ss:num. e-1 <= ss /\
                           G = 2 EXP ss`,`ss:num`) (CONJ (ASSUME `e-1 <= ss`)
                            th)) else NO_TAC) THEN
  MP_TAC(ISPEC `1..(2*e)` FAMILY_NONHOMOG_BND) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC CARD_2E_GT2 THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Cf:int` (LABEL_TAC "FAM")) THEN
  X_GEN_TAC `cpsi:int` THEN DISCH_TAC THEN
  X_GEN_TAC `B:int` THEN STRIP_TAC THEN
  ABBREV_TAC `Cm0:int = B * &5 pow (G-k) * &2 pow (k-(e-1))` THEN
  ABBREV_TAC `Cfp:int = abs Cf + &1` THEN
  SUBGOAL_THEN `&1 <= (Cm0:int)` ASSUME_TAC THENL
   [EXPAND_TAC "Cm0" THEN MATCH_MP_TAC INT_ONE_LE_MUL THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_ONE_LE_MUL THEN CONJ_TAC THEN
     MATCH_MP_TAC INT_POW_LE_1 THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (Cfp:int) /\ Cf <= Cfp` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Cfp" THEN CONJ_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &G * &e * (cpsi:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_ONE_LE_MUL THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
      MATCH_MP_TAC INT_ONE_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `(&5 pow (G-1) * (Cm0:int)) pow (2*e) * (Cfp * (&G * &e * cpsi) pow
   (2*e-1)) * (&2 pow (e+1)) pow (2*e-1) + (&4 * &G * &e * cpsi) pow
    (4*e*G)` THEN
  SUBGOAL_THEN `&1 <= &5 pow (G-1) * (Cm0:int)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_ONE_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC INT_POW_LE_1 THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= (&5 pow (G-1) * (Cm0:int)) pow (2*e) * (Cfp * (&G * &e * cpsi)
   pow (2*e-1)) * (&2 pow (e+1)) pow (2*e-1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_ONE_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC INT_POW_LE_1 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC INT_ONE_LE_MUL THEN CONJ_TAC THENL
       [MATCH_MP_TAC INT_ONE_LE_MUL THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC INT_POW_LE_1 THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INT_POW_LE_1 THEN MATCH_MP_TAC INT_POW_LE_1 THEN
         INT_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (&4 * &G * &e * (cpsi:int)) pow (4*e*G)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_POW_LE THEN
    REPEAT(MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC]) THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`PSI:(num->int)->num->num->int`; `P:int`] THEN
   STRIP_TAC THEN
  ASM_CASES_TAC `&2 * (&G * &e * (cpsi:int) * (&2 * P) pow (e-1)) <= (&2 * P) pow
   (2*e-1)` THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `((&5 pow (G-1) * (Cm0:int)) pow (2*e) * (Cfp * (&G * &e * cpsi) pow
     (2*e-1)) * (&2 pow (e+1)) pow (2*e-1)) * P pow (2*(2*e*G) - e)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2*(2*e*G)-e = 2*2*e*G-e`] THEN
      MATCH_MP_TAC WIDE_CORE_BND_W THEN
      MAP_EVERY EXISTS_TAC [`k:num`; `B:int`; `Cf:int`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[ARITH_RULE `2*(2*e*G)-e = 2*2*e*G-e`] THEN
      MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
       [REWRITE_TAC[INT_LE_ADDR] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC]];
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `(&4 * &G * &e * (cpsi:int)) pow (4*e*G)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SMALLP_CORE_BND THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `(&5 pow (G-1) * (Cm0:int)) pow (2*e) * (Cfp * (&G * &e * cpsi) pow
     (2*e-1)) * (&2 pow (e+1)) pow (2*e-1) + (&4 * &G * &e * cpsi) pow
      (4*e*G)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INT_LE_ADDL] THEN ASM_INT_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_RID] THEN
      MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
       [ASM_INT_ARITH_TAC;
        MATCH_MP_TAC INT_POW_LE_1 THEN ASM_REWRITE_TAC[]]]]);;

let DP_PSI_FIBERSUM_BND_W = prove
 (`!e. 2 <= e ==> DPWIH2 (e-1)
     ==> ?kk. e <= 2*kk /\ 1 <= kk /\
            !cpsi:int. &1 <= cpsi
            ==> ?cc. &1 <= cc /\
            !(PSI:(num->int)->num->num->int) (P:int). &1 <= P /\
                    (!(hh:num->int) i. (!l. l IN 1..kk ==> abs(hh l) <= &2 * P)
                     /\ i IN 1..kk ==> ~(PSI hh i (e-1) = &0)) /\
                    (!(hh:num->int) i j. (!l. l IN 1..kk ==> abs(hh l) <= &2 *
                     P) /\ i IN 1..kk /\ j <= (e-1)
                         ==> abs(PSI hh i j) <= cpsi * (&2 * P) pow ((e-1) -
                          j))
                    ==> &(nsum (ibox kk (&2 * P))
                           (\hh. CARD {y:num->int | y IN ibox kk (&2 * P) /\
                                isum(1..kk)(\i. hh i * ipoly (PSI hh i) (e-1)
                                 (y i)) = &0}))
                        <= cc * P pow (2*kk - e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e-1` SIGNED_GROUP_MULT_W) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `1 <= 2 EXP k /\ k <= 2 EXP k /\
   e - 1 <= 2 EXP k` STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `k:num` LT_POW2_REFL) THEN
    REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n=0)`; EXP_EQ_0] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `2*e*2 EXP k` THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[ARITH_RULE `2*2*e*n = e*(4*n)`] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `e = e * 1`] THEN
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[ARITH_RULE `1 <= 4 * n <=> ~(n = 0)`; EXP_EQ_0] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n=0)`; MULT_EQ_0; EXP_EQ_0;
     ARITH] THEN
    UNDISCH_TAC `2 <= e` THEN ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `cpsi:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try fst(dest_var(fst(dest_forall(concl th))))="A"
   with _ -> false)
                          then MP_TAC(SPEC `cpsi:int` th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`e:num`;`k:num`;`2 EXP k`] WARING_PSI_FIBER_TOWER_W) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `cpsi:int`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `B:int`) THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL
   [MAP_EVERY X_GEN_TAC [`psi:num->int`; `neg:num->bool`; `GG:num`; `M:int`;
     `z:int`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if (try fst(dest_var(fst(dest_forall(concl
     th))))="psi" with _ -> false)
                            then MATCH_MP_TAC th else NO_TAC) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN ACCEPT_TAC]);;

let MONO_FINDIFF_LEAD_BND = prove
 (`!e P h:int. &1 <= P /\ abs h <= &2 * P
   ==> ?g. (!y:int. (y+h) pow (SUC e) = y pow (SUC e) + h * isum(0..e)(\j. g j
    * y pow j)) /\
           g e = &(SUC e) /\
           (!j. j <= e ==> abs(g j) <= &(4 EXP (SUC e)) * P pow (e - j))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `(\j. &1):num->int` THEN
    REWRITE_TAC[ISUM_SING_NUMSEG; INT_POW_1; INT_POW; INT_MUL_RID] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[ARITH] THEN INT_ARITH_TAC;
      REWRITE_TAC[LE] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SUB_REFL; INT_POW; INT_MUL_RID; INT_ABS_NUM] THEN
      REWRITE_TAC[INT_OF_NUM_LE] THEN REWRITE_TAC[EXP_1] THEN ARITH_TAC];
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL [`P:int`; `h:int`]) THEN ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `g0:num->int` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `\j. (if j = 0 then &0 else g0(j - 1)) + (if j <= e then h * g0 j
    else &0) + (if j = SUC e then &1 else &0):int` THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN
     SUBGOAL_THEN
      `isum (0..SUC e) (\j. ((if j =
       0 then &0 else g0 (j - 1)) + (if j <= e then h * g0 j else &0) + (if j =
        SUC e then &1 else &0)) * y pow j) = y pow (SUC e) + y * isum(0..e)(\j.
         g0 j * y pow j) + h * isum(0..e)(\j. g0 j * y pow j)`
      (LABEL_TAC "KEY") THENL
      [REWRITE_TAC[INT_ADD_RDISTRIB] THEN
       SIMP_TAC[ISUM_ADD; FINITE_NUMSEG] THEN
       SUBGOAL_THEN `(\j. (if j = SUC e then &1 else &0) * (y:int) pow j) = (\j. if j
        = SUC e then y pow (SUC e) else &0)` SUBST1_TAC THENL
        [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN COND_CASES_TAC THEN
         ASM_REWRITE_TAC[INT_MUL_LID; INT_MUL_LZERO]; ALL_TAC] THEN
       SIMP_TAC[ISUM_DELTA; IN_NUMSEG; LE_0; LE_REFL] THEN
       SUBGOAL_THEN `isum (0..SUC e) (\j. (if j <= e then h * g0 j else &0) * y
        pow j) = h * isum(0..e)(\j. g0 j * y pow j)` SUBST1_TAC THENL
        [REWRITE_TAC[ISUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC e <= e)`;
          INT_MUL_LZERO; INT_ADD_RID] THEN
         REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC ISUM_EQ THEN
          X_GEN_TAC `j:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
           ASM_REWRITE_TAC[] THEN CONV_TAC INT_RING; ALL_TAC] THEN
       REWRITE_TAC[POLY_REINDEX; GSYM IPOLY_SHIFT_SUM] THEN INT_ARITH_TAC;
       ALL_TAC] THEN
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN ASM_REWRITE_TAC[] THEN
     SUBGOAL_THEN `((y:int) + h) pow SUC(SUC e) = (y + h) * (y pow SUC e + h *
      isum(0..e)(\j. g0 j * y pow j))` SUBST1_TAC THENL
      [GEN_REWRITE_TAC LAND_CONV [INT_POW] THEN
       ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `(y:int) pow SUC(SUC e) = y * y pow SUC e` SUBST1_TAC THENL
      [REWRITE_TAC[INT_POW]; ALL_TAC] THEN
     CONV_TAC INT_RING;
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     REWRITE_TAC[ARITH_RULE `~(SUC e = 0)`; ARITH_RULE `~(SUC e <= e)`;
       SUC_SUB1; LE_REFL] THEN
     ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
      INT_ARITH_TAC;
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     MATCH_MP_TAC MFB_COEFF_BND THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let PHI_PACK_LEAD_BND = prove
 (`!n nn f (h:int) c P. &1 <= P /\ abs h <= &2 * P /\ &0 <= c /\ SUC n <= nn /\
     (!i. i <= SUC n ==> abs(f i) <= c * P pow (nn - i))
    ==> ?psi. (!y. ipoly f (SUC n) (y+h) - ipoly f (SUC n) y = h * ipoly psi n
     y) /\
              psi n = &(SUC n) * f (SUC n) /\
              (!j. j <= n ==> abs(psi j) <= &2 * &(4 EXP (SUC n)) * c * P pow
               (nn - 1 - j))`,
  INDUCT_TAC THEN REPEAT STRIP_TAC THENL
   [EXISTS_TAC `(\j. (f:num->int) 1):num->int` THEN
    SUBGOAL_THEN `!z. ipoly (\j. (f:num->int) 1) 0 z = f 1` (fun th ->
     REWRITE_TAC[th]) THENL
     [GEN_TAC THEN
      REWRITE_TAC[ipoly; ISUM_SING_NUMSEG; INT_POW; INT_MUL_RID]; ALL_TAC] THEN
    REWRITE_TAC[ARITH_RULE `SUC 0 = 1`; IPOLY1] THEN
    CONJ_TAC THENL [GEN_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[LE] THEN GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC 0`; INT_MUL_RID; EXP_1; SUB_0] THEN
     DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= (c:int) * P pow (nn-1)` ASSUME_TAC THENL
     [MATCH_MP_TAC INT_LE_MUL THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`abs ((f:num->int) 1) <= c * P pow (nn - 1)`;
      `&0 <= (c:int) * P pow (nn-1)`] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
   FIRST_X_ASSUM(MP_TAC o SPECL
    [`nn:num`;`f:num->int`;`h:int`;`c:int`;`P:int`]) THEN
   ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
      [ASM_ARITH_TAC;
       X_GEN_TAC `i:num` THEN DISCH_TAC THEN
       FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) &&
        not(is_forall(snd(dest_forall(concl th)))))) THEN ASM_ARITH_TAC];
     ALL_TAC] THEN
   DISCH_THEN(X_CHOOSE_THEN `psiP:num->int` STRIP_ASSUME_TAC) THEN
   MP_TAC(SPECL [`SUC n`;`P:int`;`h:int`] MONO_FINDIFF_LEAD_BND) THEN
    ASM_REWRITE_TAC[] THEN
   DISCH_THEN(X_CHOOSE_THEN `g:num->int` STRIP_ASSUME_TAC) THEN
   EXISTS_TAC `\j. (if j <= n then psiP j else &0) + (f:num->int)(SUC(SUC n)) *
    g j :int` THEN
   REPEAT CONJ_TAC THENL
    [GEN_TAC THEN
     GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [IPOLY_SUC] THEN
     GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [IPOLY_SUC] THEN
     SUBGOAL_THEN `ipoly (\j. (if j <= n then psiP j else &0) +
      (f:num->int)(SUC(SUC n)) * g j) (SUC n) y =
                   ipoly psiP n y + f(SUC(SUC n)) * isum(0..SUC n)(\j. g j * y
                    pow j)` SUBST1_TAC THENL
      [REWRITE_TAC[ipoly] THEN CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
       REWRITE_TAC[INT_ADD_RDISTRIB] THEN
        SIMP_TAC[ISUM_ADD; FINITE_NUMSEG] THEN
       BINOP_TAC THENL
        [REWRITE_TAC[ISUM_CLAUSES_NUMSEG; LE_0; ARITH_RULE `~(SUC n <= n)`;
          INT_MUL_LZERO; INT_ADD_RID] THEN
         MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `j:num` THEN
          REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
         ASM_REWRITE_TAC[];
         REWRITE_TAC[GSYM ISUM_LMUL] THEN MATCH_MP_TAC ISUM_EQ THEN
          X_GEN_TAC `j:num` THEN
         REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN CONV_TAC INT_RING];
       ALL_TAC] THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `y:int` o check(fun th -> is_forall(concl
      th))) THEN
     FIRST_X_ASSUM(MP_TAC o SPEC `y:int` o check(fun th -> is_forall(concl
      th))) THEN
     REWRITE_TAC[IPOLY_SUC] THEN CONV_TAC INT_RING;
     CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
      REWRITE_TAC[ARITH_RULE `~(SUC n <= n)`] THEN
     ASM_REWRITE_TAC[INT_ADD_LID] THEN REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN
      INT_ARITH_TAC;
     X_GEN_TAC `j:num` THEN DISCH_TAC THEN
      CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
     MATCH_MP_TAC INT_LE_TRANS THEN
     EXISTS_TAC `abs(if j <= n then psiP j else &0) + abs((f:num->int)(SUC(SUC
      n)) * g j)` THEN
     CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
     SUBGOAL_THEN `&0 <= (P:int) /\ &0 <= P pow (nn - 1 - j) /\
      &0 <= P pow (SUC n - j) /\
       P pow (SUC n - j) <= P pow (nn - 1 - j)` STRIP_ASSUME_TAC THENL
      [REPEAT CONJ_TAC THENL
        [ASM_INT_ARITH_TAC;
         MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC;
         MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC;
         MATCH_MP_TAC INT_POW_MONO THEN CONJ_TAC THENL
          [ASM_INT_ARITH_TAC; ASM_ARITH_TAC]]; ALL_TAC] THEN
     SUBGOAL_THEN `&0 <= (c:int) * P pow (nn - 1 - j)` ASSUME_TAC THENL
      [MATCH_MP_TAC INT_LE_MUL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN `&0 <= &2 * &(4 EXP SUC n) * (c:int) * P pow (nn - 1 - j)`
      ASSUME_TAC THENL
      [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
       [INT_ARITH_TAC; ALL_TAC] THEN
       MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
        [REWRITE_TAC[INT_POS]; FIRST_X_ASSUM ACCEPT_TAC]; ALL_TAC] THEN
     SUBGOAL_THEN `abs(if j <= n then (psiP:num->int) j else &0) <=
      &2 * &(4 EXP (SUC n))
      * c * P pow (nn - 1 - j)` ASSUME_TAC THENL
      [COND_CASES_TAC THENL
        [FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) &&
          free_in `psiP:num->int` (concl th) &&
          free_in `c:int` (concl th))) THEN ASM_REWRITE_TAC[];
         REWRITE_TAC[INT_ABS_NUM] THEN ASM_REWRITE_TAC[]];
       ALL_TAC] THEN
     SUBGOAL_THEN `abs((f:num->int)(SUC(SUC n)) * g j) <= &(4 EXP (SUC(SUC n)))
      * c * P pow (nn - 1 - j)` ASSUME_TAC THENL
      [REWRITE_TAC[INT_ABS_MUL] THEN MATCH_MP_TAC INT_LE_TRANS THEN
       EXISTS_TAC `((c:int) * P pow (nn - SUC(SUC n))) * (&(4 EXP SUC(SUC n)) * P pow
        (SUC n - j))` THEN
       CONJ_TAC THENL
        [MATCH_MP_TAC INT_LE_MUL2 THEN REWRITE_TAC[INT_ABS_POS] THEN
         CONJ_TAC THENL
          [FIRST_X_ASSUM(MP_TAC o SPEC `SUC(SUC n)` o check(fun th ->
           is_forall(concl th) && not(free_in `psiP:num->int` (concl th)) &&
            not(free_in `g:num->int` (concl th)))) THEN REWRITE_TAC[LE_REFL];
           FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> is_forall(concl th) &&
            free_in `g:num->int` (concl th))) THEN ASM_REWRITE_TAC[]];
         SUBGOAL_THEN `((c:int) * P pow (nn - SUC(SUC n))) * (&(4 EXP SUC(SUC n)) * P
          pow (SUC n - j)) = &(4 EXP SUC(SUC n)) * c * (P pow (nn - SUC(SUC n))
           * P pow (SUC n - j))` SUBST1_TAC THENL
          [REWRITE_TAC[INT_MUL_AC]; ALL_TAC] THEN
         REWRITE_TAC[GSYM INT_POW_ADD] THEN
         SUBGOAL_THEN `(nn - SUC(SUC n)) + (SUC n - j) = nn - 1 - j`
          SUBST1_TAC THENL
          [ASM_ARITH_TAC; ALL_TAC] THEN
         REWRITE_TAC[INT_MUL_ASSOC; INT_LE_REFL]];
       ALL_TAC] THEN
     MATCH_MP_TAC INT_LE_TRANS THEN
     EXISTS_TAC `&2 * &(4 EXP (SUC n)) * (c:int) * P pow (nn - 1 - j) + &(4 EXP
      (SUC(SUC n))) * c * P pow (nn - 1 - j)` THEN
     CONJ_TAC THENL [MATCH_MP_TAC INT_LE_ADD2 THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
     SUBGOAL_THEN
      `&2 * &(4 EXP (SUC n)) * (c:int) * P pow (nn - 1 - j) + &(4 EXP (SUC(SUC n))) *
       c * P pow (nn - 1 - j) = (&2 * &(4 EXP (SUC n)) + &(4 EXP (SUC(SUC n))))
        * (c * P pow (nn - 1 - j)) /\
       &2 * &(4 EXP SUC (SUC n)) * c * P pow (nn - 1 - j) = (&2 * &(4 EXP
        SUC(SUC n))) * (c * P pow (nn - 1 - j))`
      (fun th -> REWRITE_TAC[CONJUNCT1 th; CONJUNCT2 th]) THENL
      [CONJ_TAC THEN INT_ARITH_TAC; ALL_TAC] THEN
     MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
      [SUBGOAL_THEN `4 EXP SUC(SUC n) = 4 * 4 EXP SUC n` SUBST1_TAC THENL
       [REWRITE_TAC[EXP] THEN ARITH_TAC; ALL_TAC] THEN
       REWRITE_TAC[GSYM INT_OF_NUM_MUL] THEN INT_ARITH_TAC;
       ASM_REWRITE_TAC[]]]);;

let PHI_PACK_E = prove
 (`!e f (h:int) c P. 2 <= e /\ &1 <= P /\ abs h <= &2 * P /\ &0 <= c /\
     (!i. i <= e ==> abs(f i) <= c * P pow (e - i))
    ==> ?psi. (!y. ipoly f e (y+h) - ipoly f e y = h * ipoly psi (e-1) y) /\
              psi (e-1) = &e * f e /\
              (!j. j <= e-1 ==> abs(psi j) <= &2 * &(4 EXP e) * c * P pow
               ((e-1) - j))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. e = SUC n` (CHOOSE_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `e - 1` THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`n:num`;`SUC n`;`f:num->int`;`h:int`;`c:int`;`P:int`]
   PHI_PACK_LEAD_BND) THEN
  ASM_REWRITE_TAC[LE_REFL; SUC_SUB1] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:num->int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `psi:num->int` THEN ASM_REWRITE_TAC[SUC_SUB1] THEN
  X_GEN_TAC `j:num` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check(fun th -> is_forall(concl th)))
   THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `SUC n - 1 - j = n - j` (fun th -> REWRITE_TAC[th]) THENL
   [ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[]);;

let FIBER_PSIFAM = prove
 (`!(ffam:num->num->int) e kk c P (hh:num->int).
     2 <= e /\ &1 <= P /\ &0 <= c /\
      (!i. i IN 1..kk ==> abs(hh i) <= &2 * P) /\
     (!j i. j IN 1..kk /\ i <= e ==> abs(ffam j i) <= c * P pow (e - i))
     ==> ?psifam. (!i. i IN 1..kk
                       ==> (!y. ipoly (ffam i) e (y + hh i) - ipoly (ffam i) e
                        y = hh i * ipoly (psifam i) (e-1) y) /\
                           psifam i (e-1) = &e * ffam i e /\
                           (!j. j <= e-1 ==> abs(psifam i j) <= &2 * &(4 EXP e)
                            * c * P pow ((e-1) - j)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i. ?psi. i IN 1..kk
              ==> (!y. ipoly ((ffam:num->num->int) i) e (y + hh i) - ipoly
               (ffam i) e y = hh i * ipoly psi (e-1) y) /\
                  psi (e-1) = &e * ffam i e /\
                  (!j. j <= e-1 ==> abs(psi j) <= &2 * &(4 EXP e) * c * P pow
                   ((e-1) - j))`
   MP_TAC THENL
   [X_GEN_TAC `i:num` THEN ASM_CASES_TAC `i IN 1..kk` THENL
     [MP_TAC(SPECL [`e:num`;`(ffam:num->num->int) i`;`(hh:num->int)
      i`;`c:int`;`P:int`] PHI_PACK_E) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> (try
          fst(dest_forall(concl th))=`i:num` with _ -> false) &&
           not(is_conj(snd(dest_forall(concl th)))))) THEN ASM_REWRITE_TAC[];
          X_GEN_TAC `i':num` THEN DISCH_TAC THEN
           FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> free_in
            `ffam:num->num->int` (concl th))) THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(X_CHOOSE_TAC `psi:num->int`) THEN
         EXISTS_TAC `psi:num->int` THEN ASM_REWRITE_TAC[]];
      EXISTS_TAC `(\j. &0):num->int` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[SKOLEM_THM] THEN
     DISCH_THEN(X_CHOOSE_TAC `psifam:num->num->int`) THEN
    EXISTS_TAC `psifam:num->num->int` THEN ASM_REWRITE_TAC[]]);;

let FIBER_AS_PSISUM = prove
 (`!(ffam:num->num->int) (psifam:num->num->int) e kk (hh:num->int)
  (y:num->int).
     (!i. i IN 1..kk ==> !z. ipoly (ffam i) e (z + hh i) - ipoly (ffam i) e z =
      hh i * ipoly (psifam i) (e-1) z)
     ==> isum(1..kk)(\i. ipoly (ffam i) e (y i + hh i) - ipoly (ffam i) e (y
      i)) =
         isum(1..kk)(\i. hh i * ipoly (psifam i) (e-1) (y i))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ISUM_EQ THEN X_GEN_TAC `i:num` THEN
   DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `(y:num->int) i`) THEN REWRITE_TAC[]);;

let PSIFAM_UNIFORM = prove
 (`!(ffam:num->num->int) e kk (c:int) (P:int).
     2 <= e /\ &1 <= P /\ &0 <= c /\
     (!j i. j IN 1..kk /\ i <= e ==> abs(ffam j i) <= c * P pow (e - i))
     ==> ?PSI. !(hh:num->int). (!i. i IN 1..kk ==> abs(hh i) <= &2 * P)
             ==> !i. i IN 1..kk
                 ==> (!y. ipoly (ffam i) e (y + hh i) - ipoly (ffam i) e y = hh
                  i * ipoly (PSI hh i) (e-1) y) /\
                     PSI hh i (e-1) = &e * ffam i e /\
                     (!j. j <= e-1 ==> abs(PSI hh i j) <= &2 * &(4 EXP e) * c *
                      P pow ((e-1) - j))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
   X_GEN_TAC `hh:num->int` THEN
  ASM_CASES_TAC `!i. i IN 1..kk ==> abs((hh:num->int) i) <= &2 * P` THENL
   [MP_TAC(SPECL
    [`ffam:num->num->int`;`e:num`;`kk:num`;`c:int`;`P:int`;`hh:num->int`]
     FIBER_PSIFAM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `psifam:num->num->int`) THEN
    EXISTS_TAC `psifam:num->num->int` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `(\i j. &0):num->num->int` THEN ASM_REWRITE_TAC[]]);;

let FIBERSUM_TO_PSI = prove
 (`!(ffam:num->num->int) e kk (P:int) (PSI:(num->int)->num->num->int).
     (!(hh:num->int). (!i. i IN 1..kk ==> abs(hh i) <= &2 * P)
             ==> !i. i IN 1..kk
                 ==> (!y. ipoly (ffam i) e (y + hh i) - ipoly (ffam i) e y = hh
                  i * ipoly (PSI hh i) (e-1) y))
     ==> nsum (ibox kk (&2 * P))
            (\hh. CARD {y:num->int | y IN ibox kk (&2 * P) /\
                 isum(1..kk)(\i. ipoly (ffam i) e (y i + hh i) - ipoly (ffam i)
                  e (y i)) = &0})
         = nsum (ibox kk (&2 * P))
            (\hh. CARD {y:num->int | y IN ibox kk (&2 * P) /\
                 isum(1..kk)(\i. hh i * ipoly (PSI hh i) (e-1) (y i)) = &0})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC NSUM_EQ THEN X_GEN_TAC `hh:num->int` THEN
   DISCH_TAC THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  AP_TERM_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
   X_GEN_TAC `y:num->int` THEN
  MATCH_MP_TAC(TAUT `(b<=>c) ==> (a/\b<=>a/\c)`) THEN
  SUBGOAL_THEN `(!i. i IN 1..kk ==> abs((hh:num->int) i) <= &2 * P)`
   ASSUME_TAC THENL
   [UNDISCH_TAC `(hh:num->int) IN ibox kk (&2 * P)` THEN
    REWRITE_TAC[ibox; IN_ELIM_THM; IN_NUMSEG] THEN
    STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN
     FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`ffam:num->num->int`;`(PSI:(num->int)->num->num->int)
   hh`;`e:num`;`kk:num`;`hh:num->int`;`y:num->int`] FIBER_AS_PSISUM) THEN
  ANTS_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `hh:num->int`) THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]]);;

let DP_FIBER_CLOSE_W = prove
 (`!e. 2 <= e ==> DPWIH2 (e-1)
      ==> ?kk. e <= 2*kk /\
             !A:int. &1 <= A ==> ?c. &1 <= c /\
             !(ffam:num->num->int) (P:int). &1 <= P /\
              (!j. j IN 1..kk ==> ~(ffam j e = &0)) /\
                 (!j j'. j IN 1..kk /\
                  j' IN 1..kk ==> abs(ffam j e) = abs(ffam j' e)) /\
                 (!j i. j IN 1..kk /\
                  i <= e ==> abs(ffam j i) <= A * P pow (e - i))
                 ==> &(CARD (findiffset_dp ffam e kk P)) <= c * P pow (2*kk -
                  e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:num` DP_PSI_FIBERSUM_BND_W) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `kk:num` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&2 * &(4 EXP e) * A:int` o check(fun th -> (try
   fst(dest_forall(concl th))=`cpsi:int` with _ -> false))) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `A:int` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM INT_MUL_LID] THEN
     REWRITE_TAC[INT_MUL_ASSOC] THEN
    MATCH_MP_TAC INT_LE_RMUL THEN CONJ_TAC THENL
     [SIMP_TAC[INT_OF_NUM_MUL; INT_OF_NUM_LE] THEN
      REWRITE_TAC[ARITH_RULE `1 <= 2 * n <=> 1 <= n`] THEN
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
       REWRITE_TAC[EXP_EQ_0] THEN ARITH_TAC;
      ASM_INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `cc:int` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`ffam:num->num->int`; `P:int`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`ffam:num->num->int`;`e:num`;`kk:num`;`P:int`]
   FINDIFFSET_FIBERSUM_DP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(SPECL [`ffam:num->num->int`;`e:num`;`kk:num`;`A:int`;`P:int`]
   PSIFAM_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `PSI:(num->int)->num->num->int` (LABEL_TAC
   "PSIFAM")) THEN
  SUBGOAL_THEN
   `!(hh:num->int). (!i. i IN 1..kk ==> abs(hh i) <= &2 * P)
       ==> !i. i IN 1..kk ==> (!y. ipoly (ffam i) e (y + hh i) - ipoly (ffam i)
        e y = hh i * ipoly ((PSI:(num->int)->num->num->int) hh i) (e-1) y)`
   (LABEL_TAC "EQ") THENL
   [X_GEN_TAC `hh:num->int` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN
    USE_THEN "PSIFAM" (MP_TAC o SPEC `hh:num->int`) THEN
     ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "EQ" (fun eq -> MP_TAC(MATCH_MP (SPECL
   [`ffam:num->num->int`;`e:num`;`kk:num`;`P:int`;
     `PSI:(num->int)->num->num->int`] FIBERSUM_TO_PSI) eq)) THEN
  DISCH_THEN SUBST1_TAC THEN
  FIRST_X_ASSUM(fun th -> if (try fst(dest_forall(concl
   th))=`PSI:(num->int)->num->num->int` with _ -> false) then MP_TAC(SPECL
    [`PSI:(num->int)->num->num->int`;`P:int`] th) else NO_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`hh:num->int`;`i:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `PSI (hh:num->int) i (e-1) = &e * (ffam:num->num->int) i e`
     SUBST1_TAC THENL
     [USE_THEN "PSIFAM" (MP_TAC o SPEC `hh:num->int`) THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[INT_ENTIRE; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM(MATCH_MP_TAC o check(fun th -> (try fst(dest_forall(concl
       th))=`j:num` with _ -> false) && not(is_conj(snd(strip_forall(concl
        th)))) && is_neg(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`hh:num->int`;`i:num`;`j:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs((PSI:(num->int)->num->num->int) hh i j) <= &2 * &(4 EXP
     e) * A * P pow ((e-1) - j)` MP_TAC THENL
     [USE_THEN "PSIFAM" (MP_TAC o SPEC `hh:num->int`) THEN
      ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `&2 * &(4 EXP e) * (A:int) * P pow ((e-1) - j)` THEN
     ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM INT_MUL_ASSOC] THEN MATCH_MP_TAC INT_LE_LMUL THEN
     CONJ_TAC THENL
     [INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
     [REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_LMUL THEN CONJ_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC INT_POW_LE2 THEN ASM_INT_ARITH_TAC]);;

let DPWIH2_STEP = prove
 (`!e. 2 <= e ==> DPWIH2 (e-1) ==> DPWIH2 e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:num` DP_FIBER_CLOSE_W) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:num` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[DPWIH2] THEN EXISTS_TAC `2*kk` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `A:int` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `A:int` o check(fun th -> (try
   fst(dest_forall(concl th))=`A:int` with _ -> false))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:int` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:int` THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`ffam:num->num->int`; `P:int`; `m:int`] THEN
   STRIP_TAC THEN
  SUBGOAL_THEN `1 <= kk` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD (findiffset_dp (ffam:num->num->int) e kk P)) <= (c:int) * P
   pow (2 * kk - e)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_forall(concl
    th))=`ffam:num->num->int` with _ -> false) then MP_TAC(SPECL
     [`ffam:num->num->int`;`P:int`] th) else NO_TAC) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(j:num) IN 1..kk` THEN REWRITE_TAC[IN_NUMSEG] THEN
         ASM_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`j:num`;`j':num`] THEN STRIP_TAC THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(j:num) IN 1..kk` THEN
         UNDISCH_TAC `(j':num) IN 1..kk` THEN REWRITE_TAC[IN_NUMSEG] THEN
          ASM_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`j:num`;`i:num`] THEN STRIP_TAC THEN
         FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(j:num) IN 1..kk` THEN REWRITE_TAC[IN_NUMSEG] THEN
         ASM_ARITH_TAC];
      REWRITE_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `&(CARD (findiffset_dp (\n. (ffam:num->num->int)(n+kk)) e kk P))
   <= (c:int) * P pow (2 * kk - e)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if (try fst(dest_forall(concl
    th))=`ffam:num->num->int` with _ -> false) then MP_TAC(SPECL [`\n.
     (ffam:num->num->int)(n+kk)`;`P:int`] th) else NO_TAC) THEN
    CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(fun th -> if (try fst(dest_forall(concl th))=`j:num` with
         _ -> false) && not(is_conj(snd(dest_forall(concl th)))) then
          MATCH_MP_TAC th else NO_TAC) THEN
        UNDISCH_TAC `(j:num) IN 1..kk` THEN REWRITE_TAC[IN_NUMSEG] THEN
         ASM_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`j:num`;`j':num`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th -> if (try fst(dest_forall(concl th))=`j:num` with
         _ -> false) && (length(fst(strip_forall(concl th)))=2) then
          MATCH_MP_TAC th else NO_TAC) THEN
        REWRITE_TAC[IN_NUMSEG] THEN
         RULE_ASSUM_TAC(REWRITE_RULE[IN_NUMSEG]) THEN ASM_ARITH_TAC;
        MAP_EVERY X_GEN_TAC [`j:num`;`i:num`] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(fun th -> if (try fst(dest_forall(concl th))=`j:num` with
         _ -> false) then MATCH_MP_TAC th else NO_TAC) THEN
        UNDISCH_TAC `(j:num) IN 1..kk` THEN REWRITE_TAC[IN_NUMSEG] THEN
         ASM_ARITH_TAC];
      REWRITE_TAC[]]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\j. ipoly ((ffam:num->num->int) j) e`; `kk:num`; `P:int`;
    `m:int`] AGEN_FOLD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 <= (c:int) * P pow (2 * kk - e)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_MUL THEN CONJ_TAC THENL
    [ASM_INT_ARITH_TAC; MATCH_MP_TAC INT_POW_LE THEN
     ASM_INT_ARITH_TAC]; ALL_TAC] THEN
  ABBREV_TAC `B0 = num_of_int(c * P pow (2 * kk - e))` THEN
  SUBGOAL_THEN `&B0:int = c * P pow (2 * kk - e)` (LABEL_TAC "BE") THENL
   [EXPAND_TAC "B0" THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
    ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (findiffset_dp (ffam:num->num->int) e kk P) <= B0 /\
   CARD (findiffset_dp (\n. (ffam:num->num->int)(n+kk)) e kk P) <= B0`
    STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    USE_THEN "BE" (fun th -> REWRITE_TAC[th]) THEN
     ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {w | w IN ibox (2*kk) P /\
    isum(1..kk)(\i. mvf kk (\j. ipoly ((ffam:num->num->int) j) e) i (w
     i)) = isum((kk+1)..(2*kk))(\i. mvf kk (\j. ipoly (ffam j) e) i (w
      i))} <= B0`
   ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (findiffset_dp (ffam:num->num->int) e kk P)` THEN
     ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIAG_HEAD_LE_FDFS THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {w | w IN ibox (2*kk) P /\
    isum(1..kk)(\i. mvf kk (wtail kk (\j. ipoly ((ffam:num->num->int) j) e)) i
     (w i)) = isum((kk+1)..(2*kk))(\i. mvf kk (wtail kk (\j. ipoly (ffam j) e))
      i (w i))} <= B0`
   ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `CARD (findiffset_dp (\n. (ffam:num->num->int)(n+kk)) e kk P)`
     THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIAG_TAIL_LE_FDFS THEN
      ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `&B0:int` THEN CONJ_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_ARITH_TAC;
    USE_THEN "BE" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[INT_LE_REFL]]);;

(* Base case e = 1 of the fiber-count induction (Khinchin's r_2 <= 3P linear *)
(* count): DPWIH2 1 directly, with count constant B = 3 independent of the   *)
(* coefficient scale A.                                                      *)
let DPWIH2_BASE = prove
 (`DPWIH2 1`,
  REWRITE_TAC[DPWIH2] THEN EXISTS_TAC `2` THEN
  REWRITE_TAC[ARITH] THEN X_GEN_TAC `A:int` THEN DISCH_TAC THEN
  EXISTS_TAC `&3:int` THEN REWRITE_TAC[INT_LE_REFL] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[ARITH_RULE `2 - 1 = 1`; INT_POW_1] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `&(CARD {v:int | abs v <= P}):int` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_SIMP_TAC[ABS_SEG_CARD_LE]] THEN
  REWRITE_TAC[INT_OF_NUM_LE] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(IMAGE (\x:num->int. x 1) {x | x IN ibox 2 P /\
   isum (1..2) (\j. ipoly (ffam j) 1 (x j)) = m})` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_IMP_LE THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x:num->int`; `y:num->int`] THEN STRIP_TAC THEN
      MATCH_MP_TAC PROJ1_INJ_2_DP THEN
       MAP_EVERY EXISTS_TAC [`ffam:num->num->int`;`P:int`;`m:int`] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
       REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ibox 2 P` THEN
       REWRITE_TAC[IBOX_FINITE] THEN SET_TAC[]];
    MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[ABS_SEG_FINITE] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `v:int` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:num->int` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[ibox; IN_ELIM_THM]) THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN ASM_REWRITE_TAC[IN_NUMSEG; ARITH]]);;

let DPWIH2_ALL = prove
 (`!e. 1 <= e ==> DPWIH2 e`,
  INDUCT_TAC THEN REWRITE_TAC[ARITH] THEN DISCH_TAC THEN
  ASM_CASES_TAC `e = 0` THENL
   [ASM_REWRITE_TAC[ARITH] THEN REWRITE_TAC[DPWIH2_BASE]; ALL_TAC] THEN
  MP_TAC(SPEC `SUC e` DPWIH2_STEP) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUC_SUB1] THEN DISCH_THEN MATCH_MP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Fundamental counting lemma and the Schnirelmann-density argument          *)
(* ------------------------------------------------------------------------- *)

let FUND_LEMMA_CF = prove
 (`!e. 1 <= e
       ==> ?s c. e <= s /\ 1 <= c /\
                 !P m. rcount e s P m <= c * P EXP (s - e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:num` DPWIH2_ALL) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[DPWIH2] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `&1:int`) THEN REWRITE_TAC[INT_LE_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `B:int` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:num`; `num_of_int B`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    SUBGOAL_THEN `&(num_of_int B):int = B` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN
      ASM_INT_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`P:num`; `m:num`] THEN
  ASM_CASES_TAC `P = 0` THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `rcount e k 0 m = 0` (fun th -> REWRITE_TAC[th; LE_0]) THEN
    REWRITE_TAC[rcount] THEN
    SUBGOAL_THEN `{t | t IN boxtuples k 0 /\
     boxsum e k t = m} = {}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_ELIM_THM; boxtuples] THEN
      X_GEN_TAC `t:num->num` THEN REWRITE_TAC[IN_NUMSEG; LT] THEN
      SUBGOAL_THEN `1 <= k` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      MESON_TAC[LE_REFL; ARITH_RULE `~(x < 0)`];
      REWRITE_TAC[CARD_CLAUSES]];
    ALL_TAC] THEN
  SUBGOAL_THEN `1 <= P` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD {x | x IN ibox k (&P) /\
   isum(1..k)(\i. ipoly (monom e) e (x i)) = &m}` THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[RCOUNT_LE_SYM]; ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
  SUBGOAL_THEN `&(num_of_int B * P EXP (k - e)):int = B * (&P) pow (k - e)`
   SUBST1_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_MUL; GSYM INT_OF_NUM_POW] THEN
    SUBGOAL_THEN `&(num_of_int B):int = B` SUBST1_TAC THENL
     [MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= &P:int` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\j:num. monom e`; `&P:int`;
    `&m:int`] o check(fun th -> (try fst(dest_forall(concl
     th))=`ffam:num->num->int` with _ -> false))) THEN
  CONV_TAC(TOP_DEPTH_CONV BETA_CONV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `j:num` THEN DISCH_TAC THEN REWRITE_TAC[monom] THEN
      CONV_TAC INT_REDUCE_CONV;
      MAP_EVERY X_GEN_TAC [`j:num`;`i:num`] THEN STRIP_TAC THEN
       REWRITE_TAC[monom] THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[INT_ABS_NUM; INT_ABS_0; INT_MUL_LID] THENL
       [REWRITE_TAC[SUB_REFL; INT_POW; INT_MUL_RID] THEN
        REWRITE_TAC[INT_LE_REFL];
        MATCH_MP_TAC INT_POW_LE THEN ASM_INT_ARITH_TAC]];
    REWRITE_TAC[]]);;

let epowers = new_definition
 `epowers e = {x EXP e | x IN (:num)}`;;

let EPOWERS_0 = prove
 (`!e. 1 <= e ==> 0 IN epowers e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[epowers; IN_ELIM_THM; IN_UNIV] THEN
  EXISTS_TAC `0` THEN
   ASM_SIMP_TAC[EXP_ZERO; ARITH_RULE `1 <= e ==> ~(e = 0)`]);;

let EPOWERS_1 = prove
 (`!e. 1 IN epowers e`,
  GEN_TAC THEN REWRITE_TAC[epowers; IN_ELIM_THM; IN_UNIV] THEN
  EXISTS_TAC `1` THEN REWRITE_TAC[EXP_ONE]);;

let waring_repr = new_definition
 `waring_repr e g n <=>
    ?m f. m <= g /\ (!i. i IN 1..m ==> ?x. f i = x EXP e) /\
     n = nsum(1..m) f`;;

let WARING_ADD = prove
 (`!e a b x y. waring_repr e a x /\ waring_repr e b y
               ==> waring_repr e (a + b) (x + y)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_repr] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `m':num` (X_CHOOSE_THEN `g:num->num`
     STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `m + m':num` THEN
  EXISTS_TAC `(\i. if i <= m then (f:num->num) i else g(i - m)):num->num` THEN
  REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_NUMSEG] THEN
      ASM_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `i - m:num`) THEN
      REWRITE_TAC[IN_NUMSEG] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(\i. if i <= m then (f:num->num) i else g(i - m)):num->num`;
                 `1`; `m:num`; `m':num`] NSUM_ADD_SPLIT) THEN
  ANTS_TAC THENL [ARITH_TAC; ALL_TAC] THEN DISCH_THEN SUBST1_TAC THEN
  BINOP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NSUM_EQ THEN
    REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
     ASM_ARITH_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `m + 1 = 1 + m /\ m + m' = m' + m`] THEN
  REWRITE_TAC[NSUM_OFFSET] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC NSUM_EQ THEN
  REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
  COND_CASES_TAC THENL [ASM_ARITH_TAC; AP_TERM_TAC THEN ASM_ARITH_TAC]);;

let WARING_0 = prove
 (`!e. waring_repr e 0 0`,
  GEN_TAC THEN REWRITE_TAC[waring_repr] THEN
  MAP_EVERY EXISTS_TAC [`0`; `(\i. 0):num->num`] THEN
  SIMP_TAC[LE_REFL; NSUM_CLAUSES_NUMSEG; ARITH; IN_NUMSEG] THEN
  REPEAT STRIP_TAC THEN ASM_ARITH_TAC);;

let sumpow = new_definition
 `sumpow e s = iterate(+++) (1..s) (\i. epowers e)`;;

let SUMPOW_0 = prove
 (`!e. sumpow e 0 = {0}`,
  REWRITE_TAC[sumpow; NUMSEG_CLAUSES; ARITH] THEN
  SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_SUMSET; FINITE_EMPTY; NEUTRAL_SUMSET]);;

let SUMPOW_SUC = prove
 (`!e s. sumpow e (SUC s) = epowers e +++ sumpow e s`,
  REWRITE_TAC[sumpow; NUMSEG_CLAUSES; ARITH_RULE `1 <= SUC s`] THEN
  SIMP_TAC[ITERATE_CLAUSES; MONOIDAL_SUMSET; FINITE_NUMSEG; IN_NUMSEG;
           ARITH_RULE `~(SUC s <= s)`]);;

let SUMPOW_REPR = prove
 (`!e s n. 1 <= e /\ n IN sumpow e s
           ==> ?f. (!i. i IN 1..s ==> ?x. f i = x EXP e) /\ n = nsum(1..s) f`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[SUMPOW_0; IN_SING; NSUM_CLAUSES_NUMSEG; ARITH] THEN
    STRIP_TAC THEN EXISTS_TAC `(\i. 0):num->num` THEN
    ASM_REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUMPOW_SUC; sumset; IN_ELIM_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:num->num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `x IN epowers e` THEN
   REWRITE_TAC[epowers; IN_ELIM_THM; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:num` (ASSUME_TAC o SYM)) THEN
  EXISTS_TAC `(\i. if i = SUC s then x else (g:num->num) i):num->num` THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    COND_CASES_TAC THENL
     [ASM_MESON_TAC[];
      SUBGOAL_THEN `i IN 1..s` MP_TAC THENL
       [REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
        DISCH_THEN(fun th -> FIRST_X_ASSUM(fun a -> MP_TAC(MATCH_MP a th)))
         THEN
        SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `nsum(1..s)(\i. if i = SUC s then x else (g:num->num) i) =
   nsum(1..s) g`
    SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THENL [ASM_ARITH_TAC; REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let WARING_OF_SUMPOW = prove
 (`!e s z. 1 <= e /\ z IN sumpow e s ==> waring_repr e s z`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[waring_repr] THEN
  MP_TAC(ISPECL [`e:num`; `s:num`; `z:num`] SUMPOW_REPR) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:num->num` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`s:num`; `f:num->num`] THEN ASM_REWRITE_TAC[LE_REFL]);;

let boxreps = new_definition
 `boxreps e s P = {m | ?t. t IN boxtuples s P /\ boxsum e s t = m}`;;

let BOXTUPLES_CARD = prove
 (`!s P. CARD(boxtuples s P) = P EXP s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[boxtuples] THEN
  SUBGOAL_THEN
   `{t | (!i. i IN 1..s ==> (t:num->num) i < P) /\
         (!i. ~(i IN 1..s) ==> t i = 0)} =
    {f | (!x. x IN 1..s ==> (f:num->num) x IN {y | y < P}) /\
         (!x. ~(x IN 1..s) ==> f x = 0)}`
   SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(INST [`0`,`d:num`]
    (ISPECL [`1..s`; `{y:num | y < P}`] CARD_FUNSPACE)) THEN
  REWRITE_TAC[FINITE_NUMSEG; FINITE_NUMSEG_LT; CARD_NUMSEG_1;
    CARD_NUMSEG_LT] THEN
  DISCH_THEN ACCEPT_TAC);;

let SUMPOW_NSUM_EPOWERS = prove
 (`!e s f. (!i. i IN 1..s ==> (f:num->num) i IN epowers e)
           ==> nsum(1..s) f IN sumpow e s`,
  GEN_TAC THEN INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[SUMPOW_0; NSUM_CLAUSES_NUMSEG; ARITH; IN_SING];
    REWRITE_TAC[SUMPOW_SUC; NSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC s`] THEN
    DISCH_TAC THEN REWRITE_TAC[sumset; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`(f:num->num)(SUC s)`; `nsum(1..s) f`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN
      REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
       FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
      ARITH_TAC]]);;

let BOXREPS_SUBSET_SUMPOW = prove
 (`!e s P. boxreps e s P SUBSET sumpow e s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; boxreps; IN_ELIM_THM] THEN
  X_GEN_TAC `m:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  ASM_REWRITE_TAC[boxsum] THEN MATCH_MP_TAC SUMPOW_NSUM_EPOWERS THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  REWRITE_TAC[epowers; IN_ELIM_THM; IN_UNIV] THEN MESON_TAC[]);;

let BOXSUM_BOUND = prove
 (`!e s P t. t IN boxtuples s P ==> boxsum e s t <= s * P EXP e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[boxtuples; boxsum; IN_ELIM_THM] THEN
   STRIP_TAC THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `nsum(1..s) (\i:num. P EXP e)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_LE THEN REWRITE_TAC[FINITE_NUMSEG] THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC EXP_MONO_LE_IMP THEN MATCH_MP_TAC LT_IMP_LE THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    SIMP_TAC[NSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG_1] THEN
     REWRITE_TAC[LE_REFL]]);;

let BOXREPS_SUBSET_NUMSEG = prove
 (`!e s P. boxreps e s P SUBSET 0..(s * P EXP e)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SUBSET; boxreps; IN_ELIM_THM; IN_NUMSEG] THEN
  X_GEN_TAC `m:num` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:num->num` (STRIP_ASSUME_TAC o GSYM)) THEN
  CONJ_TAC THENL [ARITH_TAC; ASM_MESON_TAC[BOXSUM_BOUND]]);;

let BOXREPS_FINITE = prove
 (`!e s P. FINITE(boxreps e s P)`,
  MESON_TAC[BOXREPS_SUBSET_NUMSEG; FINITE_NUMSEG; FINITE_SUBSET]);;

let BOXREPS_IMAGE = prove
 (`!e s P. boxreps e s P = IMAGE (boxsum e s) (boxtuples s P)`,
  REWRITE_TAC[boxreps; EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]);;

let BOX_FIBER_PARTITION = prove
 (`!e s P. P EXP s = nsum (boxreps e s P) (\m. rcount e s P m)`,
  REPEAT GEN_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM BOXTUPLES_CARD] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM; BOXTUPLES_FINITE] THEN
  MP_TAC(ISPECL [`boxsum e s`; `(\x:num->num. 1)`; `boxtuples s P`]
    NSUM_IMAGE_GEN) THEN
  ASM_SIMP_TAC[BOXTUPLES_FINITE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[GSYM BOXREPS_IMAGE] THEN MATCH_MP_TAC NSUM_EQ THEN
  X_GEN_TAC `m:num` THEN DISCH_TAC THEN REWRITE_TAC[rcount] THEN
  MATCH_MP_TAC(GSYM CARD_EQ_NSUM) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `boxtuples s P` THEN
  ASM_SIMP_TAC[BOXTUPLES_FINITE] THEN SET_TAC[]);;

let PIGEONHOLE_BOXREPS = prove
 (`!e s c P.
        e <= s /\ 1 <= P /\ (!m. rcount e s P m <= c * P EXP (s - e))
        ==> P EXP e <= c * CARD(boxreps e s P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `P EXP s <= CARD(boxreps e s P) * (c * P EXP (s - e))`
   MP_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [BOX_FIBER_PARTITION] THEN
    MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `nsum (boxreps e s P) (\m:num. c * P EXP (s - e))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC NSUM_LE THEN ASM_SIMP_TAC[BOXREPS_FINITE];
      ASM_SIMP_TAC[NSUM_CONST; BOXREPS_FINITE; LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `P EXP s = P EXP e * P EXP (s - e)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM EXP_ADD] THEN AP_TERM_TAC THEN
    ASM_ARITH_TAC; ALL_TAC] THEN
  ONCE_REWRITE_TAC[ARITH_RULE `a * b <= c * (d * b) <=> a * b <= (c * d) * b`]
   THEN
  ASM_SIMP_TAC[LE_MULT_RCANCEL; EXP_EQ_0;
    ARITH_RULE `1 <= P ==> ~(P = 0)`] THEN
  ASM_MESON_TAC[MULT_SYM]);;

let CARD_BOXREPS_LE = prove
 (`!e s P. CARD(boxreps e s P) <= count (sumpow e s) (s * P EXP e) + 1`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `L = s * P EXP e` THEN
  SUBGOAL_THEN `FINITE(sumpow e s INTER (1..L))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_INTER THEN REWRITE_TAC[FINITE_NUMSEG]; ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `CARD(sumpow e s INTER (0..L))` THEN CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    ASM_SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[BOXREPS_SUBSET_SUMPOW; SUBSET];
      MP_TAC(SPECL [`e:num`; `s:num`; `P:num`] BOXREPS_SUBSET_NUMSEG) THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `0..L = 0 INSERT (1..L)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INSERT; IN_NUMSEG] THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[count] THEN
  ONCE_REWRITE_TAC[SET_RULE
    `(s:num->bool) INTER (0 INSERT t) =
     (if 0 IN s then 0 INSERT (s INTER t) else s INTER t)`] THEN
  COND_CASES_TAC THEN
  ASM_SIMP_TAC[CARD_CLAUSES; IN_INTER; IN_NUMSEG] THEN ARITH_TAC);;

let COUNT_KEY_BOUND = prove
 (`!e s c P.
        e <= s /\ 1 <= P /\ (!m. rcount e s P m <= c * P EXP (s - e))
        ==> P EXP e <= c * (count (sumpow e s) (s * P EXP e) + 1)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC LE_TRANS THEN
  EXISTS_TAC `c * CARD(boxreps e s P)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC PIGEONHOLE_BOXREPS THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    REWRITE_TAC[CARD_BOXREPS_LE]]);;

let COUNT_MONO_N = prove
 (`!s m n. m <= n ==> count s m <= count s n`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[count] THEN MATCH_MP_TAC CARD_SUBSET THEN
  ASM_SIMP_TAC[FINITE_INTER; FINITE_NUMSEG] THEN
  MATCH_MP_TAC(SET_RULE
    `(a:num->bool) SUBSET b ==> s INTER a SUBSET s INTER b`) THEN
  REWRITE_TAC[SUBSET_NUMSEG] THEN ASM_ARITH_TAC);;

let SUMPOW_CONTAINS_SMALL = prove
 (`!e s k. 1 <= e /\ k <= s ==> k IN sumpow e s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k = nsum(1..s) (\i:num. if i <= k then 1 else 0)`
   SUBST1_TAC THENL
   [SIMP_TAC[NSUM_CASES; FINITE_NUMSEG; IN_NUMSEG] THEN
    REWRITE_TAC[NSUM_0; ADD_CLAUSES] THEN
    SUBGOAL_THEN `{i | (1 <= i /\ i <= s) /\ i <= k} = 1..k` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_NUMSEG] THEN ASM_ARITH_TAC;
      SIMP_TAC[NSUM_CONST; FINITE_NUMSEG; CARD_NUMSEG_1; MULT_CLAUSES]];
    MATCH_MP_TAC SUMPOW_NSUM_EPOWERS THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    ASM_MESON_TAC[EPOWERS_1; EPOWERS_0]]);;

let COUNT_SUMPOW_GE1 = prove
 (`!e s n. 1 <= e /\ 1 <= s /\ 1 <= n ==> 1 <= count (sumpow e s) n`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `1 IN (sumpow e s INTER (1..n))` MP_TAC THENL
   [REWRITE_TAC[IN_INTER; IN_NUMSEG] THEN
    ASM_SIMP_TAC[SUMPOW_CONTAINS_SMALL; LE_REFL];
    REWRITE_TAC[count] THEN
    ASM_SIMP_TAC[CARD_EQ_0; FINITE_INTER; FINITE_NUMSEG;
                 ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    SET_TAC[]]);;

let SELF_LE_EXP = prove
 (`!n e. 1 <= e ==> n <= n EXP e`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [GSYM EXP_1] THEN
  ASM_CASES_TAC `n = 0` THENL
   [ASM_REWRITE_TAC[EXP_ZERO] THEN ASM_ARITH_TAC;
    ASM_SIMP_TAC[LE_EXP]]);;

let SUCC_POW_LE = prove
 (`!e P. 1 <= P ==> (P + 1) EXP e <= 2 EXP e * P EXP e`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MULT_EXP] THEN
  MATCH_MP_TAC EXP_MONO_LE_IMP THEN ASM_ARITH_TAC);;

let EXISTS_MAX_POW = prove
 (`!e s n. 1 <= e /\ 1 <= s /\ s <= n
           ==> ?P. 1 <= P /\ s * P EXP e <= n /\ n < s * (P + 1) EXP e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `\P:num. s * P EXP e <= n` num_MAX) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(?x:num. s * x EXP e <= n) /\ (?M. !x:num. s * x EXP e <= n ==> x <= M)`
   (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `1` THEN REWRITE_TAC[EXP_ONE; MULT_CLAUSES] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `n:num` THEN X_GEN_TAC `x:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `x EXP e` THEN
      ASM_SIMP_TAC[SELF_LE_EXP] THEN
      MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `s * x EXP e` THEN
      ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `a = 1 * a`] THEN
      REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `P:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `!x:num. s * x EXP e <= n ==> x <= P` THEN
    DISCH_THEN(MP_TAC o SPEC `1`) THEN
    REWRITE_TAC[EXP_ONE; MULT_CLAUSES] THEN ASM_REWRITE_TAC[] THEN
     ASM_ARITH_TAC;
    ASM_MESON_TAC[NOT_LE; ARITH_RULE `P < P + 1`]]);;

let MASTER_COUNT_BOUND = prove
 (`!e s c.
        1 <= e /\ e <= s /\ 1 <= c /\
        (!P m. rcount e s P m <= c * P EXP (s - e))
        ==> !n. 1 <= n
                ==> n <= (s * 2 EXP (e + 1) * c) * count (sumpow e s) n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = s * 2 EXP (e + 1) * c` THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `1 <= count (sumpow e s) n` ASSUME_TAC THENL
   [MATCH_MP_TAC COUNT_SUMPOW_GE1 THEN ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `n <= B:num` THENL
   [MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `B:num` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `B = B * 1`] THEN
    ASM_REWRITE_TAC[LE_MULT_LCANCEL];
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= B:num` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    SUBGOAL_THEN `1 <= 2 EXP (e + 1) * c` MP_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 1 * 1`] THEN
      MATCH_MP_TAC LE_MULT2 THEN
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC;
      REWRITE_TAC[MULT_CLAUSES] THEN DISCH_TAC THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `s = s * 1`] THEN
      ASM_REWRITE_TAC[LE_MULT_LCANCEL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s <= n:num` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`s <= B:num`; `~(n <= B:num)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:num`; `s:num`; `n:num`] EXISTS_MAX_POW) THEN
  ANTS_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`1 <= e`; `e <= s:num`; `s <= n:num`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`e:num`; `s:num`; `c:num`; `P:num`] COUNT_KEY_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `C = count (sumpow e s) n` THEN
  SUBGOAL_THEN `count (sumpow e s) (s * P EXP e) <= C` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC COUNT_MONO_N THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P EXP e <= 2 * c * C` ASSUME_TAC THENL
   [MATCH_MP_TAC LE_TRANS THEN
    EXISTS_TAC `c * (count (sumpow e s) (s * P EXP e) + 1)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `c * (C + 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
      REWRITE_TAC[LEFT_ADD_DISTRIB; MULT_CLAUSES] THEN
      MATCH_MP_TAC(ARITH_RULE `c <= c * C ==> c * C + c <= 2 * c * C`) THEN
      GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `c = c * 1`] THEN
      REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC LT_IMP_LE THEN
  MATCH_MP_TAC LTE_TRANS THEN EXISTS_TAC `s * (P + 1) EXP e` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `s * (2 EXP e * P EXP e)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    ASM_SIMP_TAC[SUCC_POW_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `s * (2 EXP e * (2 * c * C))` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[LE_MULT_LCANCEL; LE_MULT_LCANCEL] THEN DISJ2_TAC THEN
    DISJ2_TAC THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "B" THEN REWRITE_TAC[EXP_ADD; EXP_1] THEN ARITH_TAC]);;

let INV_LE_DIV = prove
 (`!n B c:real. &0 < B /\ &0 < n /\ n <= B * c ==> inv B <= c / n`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[REAL_LE_RDIV_EQ; REAL_LE_LDIV_EQ] THEN
  REWRITE_TAC[real_div] THEN
  ASM_SIMP_TAC[GSYM REAL_LE_LDIV_EQ; REAL_INV_MUL] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN
  ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
  ASM_MESON_TAC[REAL_MUL_SYM]);;

let DENSITY_POS_FROM_FUND = prove
 (`!e s c.
        1 <= e /\ e <= s /\ 1 <= c /\
        (!P m. rcount e s P m <= c * P EXP (s - e))
        ==> schnirelmann (sumpow e s) > &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`e:num`; `s:num`; `c:num`] MASTER_COUNT_BOUND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `B = s * 2 EXP (e + 1) * c` THEN
  SUBGOAL_THEN `1 <= B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    GEN_REWRITE_TAC LAND_CONV [ARITH_RULE `1 = 1 * 1 * 1`] THEN
    MATCH_MP_TAC LE_MULT2 THEN CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC LE_MULT2 THEN
      REWRITE_TAC[ARITH_RULE `1 <= x <=> ~(x = 0)`; EXP_EQ_0] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[real_gt] THEN
  MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `inv(&B)` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN REWRITE_TAC[REAL_OF_NUM_LT] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC SCHNIRELMANN_LBOUND THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MATCH_MP_TAC INV_LE_DIV THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_LT] THEN ASM_ARITH_TAC;
    REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_LE] THEN ASM_SIMP_TAC[]]);;

let DENSITY_POS = prove
 (`!e. 1 <= e ==> ?s. schnirelmann (sumpow e s) > &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:num` FUND_LEMMA_CF) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (X_CHOOSE_THEN `c:num`
   STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `s:num` THEN
  MATCH_MP_TAC DENSITY_POS_FROM_FUND THEN
  EXISTS_TAC `c:num` THEN ASM_REWRITE_TAC[]);;

let SUMPOW_BASIS = prove
 (`!e. 1 <= e
       ==> ?s k. !n. ?m f. m <= k /\ (!i. i IN 1..m ==> f i IN sumpow e s) /\
                           n = nsum(1..m) f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:num` DENSITY_POS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `s:num`) THEN
  MP_TAC(SPEC `sumpow e s` SCHNIRELMANN_DIRECT) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `k:num`) THEN
  MAP_EVERY EXISTS_TAC [`s:num`; `k:num`] THEN ASM_REWRITE_TAC[]);;

let WARING_MONO = prove
 (`!e a b n. waring_repr e a n /\ a <= b ==> waring_repr e b n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[waring_repr] THEN STRIP_TAC THEN
  ASM_MESON_TAC[LE_TRANS]);;

let WARING_FOLD = prove
 (`!e s m f. (!i. i IN 1..m ==> waring_repr e s (f i))
             ==> waring_repr e (m * s) (nsum(1..m) f)`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ARITH; MULT_CLAUSES] THENL
   [REWRITE_TAC[WARING_0]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `1 <= SUC m`] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUC m * s = m * s + s` SUBST1_TAC THENL
   [ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC WARING_ADD THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN X_GEN_TAC `i:num` THEN
    REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ASM_ARITH_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_NUMSEG] THEN ARITH_TAC]);;

let HILBERT_WARING_REPR = prove
 (`!e. 1 <= e ==> ?g. !n. waring_repr e g n`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `e:num` SUMPOW_BASIS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:num` (X_CHOOSE_TAC `k:num`)) THEN
  EXISTS_TAC `k * s:num` THEN X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n:num`) THEN
  DISCH_THEN(X_CHOOSE_THEN `m:num` (X_CHOOSE_THEN `f:num->num`
   STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC WARING_MONO THEN EXISTS_TAC `m * s:num` THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC WARING_FOLD THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC WARING_OF_SUMPOW THEN ASM_SIMP_TAC[];
    ASM_SIMP_TAC[LE_MULT_RCANCEL]]);;

let HILBERT_WARING = prove
 (`!e. 1 <= e ==> ?k. !n. ?f. n = nsum(1..k) (\i. f i EXP e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HILBERT_WARING_REPR) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `k:num` THEN
  MATCH_MP_TAC MONO_FORALL THEN X_GEN_TAC `n:num` THEN
  REWRITE_TAC[REWRITE_RULE[RIGHT_IMP_EXISTS_THM] waring_repr] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_AND_EXISTS_THM; RIGHT_AND_EXISTS_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `f:num->num`; `g:num->num`] THEN
  STRIP_TAC THEN EXISTS_TAC `\i. if i <= m then (g:num->num) i else 0` THEN
  ASM_SIMP_TAC[COND_RAND; COND_RATOR; EXP_ZERO; LE_1] THEN
  ASM_SIMP_TAC[GSYM NSUM_RESTRICT_SET; IN_NUMSEG; ARITH_RULE
   `m <= k ==> ((1 <= i /\ i <= k) /\ i <= m <=> 1 <= i /\ i <= m)`] THEN
  REWRITE_TAC[GSYM numseg] THEN MATCH_MP_TAC NSUM_EQ THEN
  ASM_REWRITE_TAC[]);;
