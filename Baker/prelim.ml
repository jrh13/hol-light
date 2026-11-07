(* ========================================================================= *)
(* Preliminaries for Baker theorem: complex integers and small sums.         *)
(*                                                                           *)
(* Purpose: closure of complex_integer (Multivariate/cauchy.ml: the numbers  *)
(* Cx x with x an integer, the elements of the subring ZinC of               *)
(* 100/transcendence.ml) under the ring operations, vsum and cproduct, and   *)
(* the bound 1 <= norm z for nonzero complex integers; splitting off the     *)
(* last term of a vsum over 1..SUC t.                                        *)
(*                                                                           *)
(* Main results: COMPLEX_INTEGER_ZINC (complex_integer z <=> z IN ZinC),     *)
(*   COMPLEX_INTEGER_CLOSED (all closure facts in one theorem) and its parts *)
(*   COMPLEX_INTEGER_CX, _CX_NUM, _ADD, _SUB, _MUL, _POW, _NEG;              *)
(*   COMPLEX_INTEGER_VSUM, COMPLEX_INTEGER_CPRODUCT, COMPLEX_INTEGER_NORM;   *)
(*   VSUM_NUMSEG_SPLIT_LAST.                                                 *)
(*                                                                           *)
(* Uses: 100/transcendence.ml (ZinC, num_in_ZinC, ZinC_subring_complex) and  *)
(*   Baker/lemmas.ml (COMPLEX_SUBRING_CLOSED,                                *)
(*   COMPLEX_SUBRING_CPRODUCT).                                              *)
(* ========================================================================= *)

needs "Baker/lemmas.ml";;

prioritize_real();;
prioritize_num();;

let COMPLEX_INTEGER_CX = prove
 (`!x. complex_integer(Cx x) <=> integer x`,
  REWRITE_TAC[complex_integer; RE_CX; IM_CX]);;

let COMPLEX_INTEGER_CX_NUM = prove
 (`!n. complex_integer(Cx(&n))`,
  REWRITE_TAC[COMPLEX_INTEGER_CX; INTEGER_CLOSED]);;

let COMPLEX_INTEGER_ZINC = prove
 (`!z. complex_integer z <=> z IN ZinC`,
  REWRITE_TAC[COMPLEX_INTEGER; ZinC; IN_ELIM_THM] THEN
  MESON_TAC[int_tybij; INTEGER_REAL_OF_INT]);;

let COMPLEX_INTEGER_CLOSED = prove
 (`(!n. complex_integer(Cx(&n))) /\
   (!x y. complex_integer x /\ complex_integer y ==> complex_integer(x + y)) /\
   (!x y. complex_integer x /\ complex_integer y ==> complex_integer(x - y)) /\
   (!x y. complex_integer x /\ complex_integer y ==> complex_integer(x * y)) /\
   (!x n. complex_integer x ==> complex_integer(x pow n)) /\
   (!x. complex_integer x ==> complex_integer(--x))`,
  REWRITE_TAC[COMPLEX_INTEGER_ZINC; num_in_ZinC] THEN
  MP_TAC(MATCH_MP COMPLEX_SUBRING_CLOSED ZinC_subring_complex) THEN
  SIMP_TAC[]);;

let COMPLEX_INTEGER_ADD = prove
 (`!x y. complex_integer x /\ complex_integer y ==> complex_integer(x + y)`,
  REWRITE_TAC[COMPLEX_INTEGER_CLOSED]);;

let COMPLEX_INTEGER_SUB = prove
 (`!x y. complex_integer x /\ complex_integer y ==> complex_integer(x - y)`,
  REWRITE_TAC[COMPLEX_INTEGER_CLOSED]);;

let COMPLEX_INTEGER_MUL = prove
 (`!x y. complex_integer x /\ complex_integer y ==> complex_integer(x * y)`,
  REWRITE_TAC[COMPLEX_INTEGER_CLOSED]);;

let COMPLEX_INTEGER_POW = prove
 (`!x n. complex_integer x ==> complex_integer(x pow n)`,
  REWRITE_TAC[COMPLEX_INTEGER_CLOSED]);;

let COMPLEX_INTEGER_NEG = prove
 (`!x. complex_integer x ==> complex_integer(--x)`,
  REWRITE_TAC[COMPLEX_INTEGER_CLOSED]);;

let COMPLEX_INTEGER_VSUM = prove
 (`!f:A->complex s.
        (!x. x IN s ==> complex_integer(f x)) ==> complex_integer(vsum s f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `vsum s (f:A->complex) = vsum s (\x. Cx(Re(f x)))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN
    ASM_MESON_TAC[complex_integer; COMPLEX_EQ; RE_CX; IM_CX];
    REWRITE_TAC[VSUM_CX; COMPLEX_INTEGER_CX] THEN
    MATCH_MP_TAC INTEGER_SUM THEN ASM_MESON_TAC[complex_integer]]);;

let COMPLEX_INTEGER_CPRODUCT = prove
 (`!f:A->complex s.
        FINITE s /\ (!x. x IN s ==> complex_integer(f x))
        ==> complex_integer(cproduct s f)`,
  SIMP_TAC[COMPLEX_INTEGER_ZINC; COMPLEX_SUBRING_CPRODUCT;
           ZinC_subring_complex]);;

let COMPLEX_INTEGER_NORM = prove
 (`!z. complex_integer z /\ ~(z = Cx(&0)) ==> &1 <= norm z`,
  REWRITE_TAC[COMPLEX_INTEGER] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CX_INJ]) THEN
  ASM_SIMP_TAC[COMPLEX_NORM_CX; REAL_ABS_INTEGER_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Small sums over initial segments of 1, 2, ....                            *)
(* ------------------------------------------------------------------------- *)

let VSUM_NUMSEG_SPLIT_LAST = prove
 (`!(f:num->complex) g t.
        (!s. 1 <= s /\ s <= t ==> g s = f s)
        ==> vsum(1..SUC t) g = vsum(1..t) f + g(SUC t)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VSUM_CLAUSES_NUMSEG; ARITH_RULE `1 <= SUC t`] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ THEN
  ASM_SIMP_TAC[IN_NUMSEG]);;
