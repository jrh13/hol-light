
labels_flag:= true;;

let dirac_delta = new_definition `dirac_delta (i:num) =
     (\j. if (i=j) then (&.1) else (&.0))`;;

let min_num = new_definition
  `min_num (X:num->bool) = @m. (m IN X) /\ (!n. (n IN X) ==> (m <= n))`;;

let min_least = prove_by_refinement (
  `!(X:num->bool) c. (X c) ==> (X (min_num X) /\ (min_num X <=| c))`,
  (* {{{ proof *)

  [
  REWRITE_TAC[min_num;IN];
  REPEAT GEN_TAC;
  DISCH_TAC;
  SUBGOAL_THEN `?n. (X:num->bool) n /\ (!m. m <| n ==> ~X m)` MP_TAC;
    REWRITE_TAC[(GSYM (ISPEC `X:num->bool` num_WOP))];
    ASM_MESON_TAC[];
  DISCH_THEN CHOOSE_TAC;
  ASSUME_TAC (select_thm `\m. (X:num->bool) m /\ (!n. X n ==> m <=| n)` `n:num`);
  ABBREV_TAC `r = @m. (X:num->bool) m /\ (!n. X n ==> m <=| n)`;
  ASM_MESON_TAC[ ARITH_RULE `~(n' < n) ==> (n <=| n') `]
  ]);;

  (* }}} *)

let max_real = new_definition(`max_real x y =
        if (y <. x) then x else y`);;

let min_real = new_definition(`min_real x y =
        if (x <. y) then x else y`);;

let deriv = new_definition(`deriv f x = @d. (f diffl d)(x)`);;
let deriv2 = new_definition(`deriv2 f = (deriv (deriv f))`);;

let square_le = prove_by_refinement(
  `!x y. (&.0 <=. x) /\ (&.0 <=. y) /\ (x*.x <=. y*.y) ==> (x <=. y)`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  UNDISCH_FIND_TAC `( *. )` ;
  ONCE_REWRITE_TAC[REAL_ARITH `(a <=. b) <=> (&.0 <= (b - a))`];
  REWRITE_TAC[GSYM REAL_DIFFSQ];
  DISCH_TAC;
  DISJ_CASES_TAC (REAL_ARITH `&.0 < (y+x) \/ (y+x <=. (&.0))`);
  MATCH_MP_TAC (SPEC `(y+x):real` REAL_LE_LCANCEL_IMP);
  ASM_REWRITE_TAC [REAL_ARITH `x * (&.0) = (&.0)`];
  CLEAN_ASSUME_TAC (REAL_ARITH `(&.0 <= y) /\ (&.0 <=. x) /\ (y+x <= (&.0)) ==> ((x= &.0) /\ (y= &.0))`);
  ASM_REWRITE_TAC[REAL_ARITH `&.0 <=. (&.0 -. (&.0))`];
  ]);;

  (* }}} *)

let max_num_sequence = prove_by_refinement(
  `!(t:num->num). (?n. !m. (n <=| m) ==> (t m = 0)) ==>
      (?M. !i. (t i <=| M))`,
  (* {{{ proof *)
  [
  GEN_TAC;
  REWRITE_TAC[GSYM LEFT_FORALL_IMP_THM];
  GEN_TAC;
  SPEC_TAC (`t:num->num`,`t:num->num`);
  SPEC_TAC (`n:num`,`n:num`);
  INDUCT_TAC;
  GEN_TAC;
  REWRITE_TAC[ARITH_RULE `0<=|m`];
  DISCH_TAC;
  EXISTS_TAC `0`;
  ASM_MESON_TAC[ARITH_RULE`(a=0) ==> (a <=|0)`];
  DISCH_ALL_TAC;
  ABBREV_TAC `b = \m. (if (m=n) then 0 else (t (m:num)) )`;
  FIRST_ASSUM (fun t-> ASSUME_TAC (SPEC `b:num->num` t));
  SUBGOAL_TAC `((b:num->num) (n) = 0) /\ (!m. ~(m=n) ==> (b m = t m))`;
  EXPAND_TAC "b";
  CONJ_TAC;
  COND_CASES_TAC;
  REWRITE_TAC[];
  ASM_MESON_TAC[];
  GEN_TAC;
  COND_CASES_TAC;
  REWRITE_TAC[];
  REWRITE_TAC[];
  DISCH_ALL_TAC;
  FIRST_ASSUM (fun t-> MP_TAC(SPEC `b:num->num` t));
  SUBGOAL_TAC `!m. (n<=|m) ==> (b m =0)`;
  GEN_TAC;
  ASM_CASES_TAC `m = (n:num)`;
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC ( `(n <=| m) /\ (~(m = n)) ==> (SUC n <=| m)`);
  ARITH_TAC;
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  ASM_MESON_TAC[]; (* good *)
  DISCH_THEN (fun t-> REWRITE_TAC[t]);
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `(M:num) + (t:num->num) n`;
  GEN_TAC;
  ASM_CASES_TAC `(i:num) = n`;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  MATCH_MP_TAC (ARITH_RULE `x <=| M ==> (x <=| M+ u)`);
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let REAL_INV_LT = prove_by_refinement(
  `!x y z. (&.0 <. x) ==> ((inv(x)*y < z) <=> (y <. x*z))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_TAC;
  REWRITE_TAC[REAL_ARITH `inv x * y = y* inv x`];
  REWRITE_TAC[GSYM real_div];
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
  REAL_ARITH_TAC;
  ]);;
  (* }}} *)

let REAL_MUL_NN = prove_by_refinement(
  `!x y. (&.0 <= x*y) <=>
    ((&.0 <= x /\ (&.0 <=. y)) \/ ((x <= &.0) /\ (y <= &.0) ))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  SUBGOAL_TAC `! x y. ((&.0 < x) ==> ((&.0 <= x*y) <=> ((&.0 <= x /\ (&.0 <=. y)) \/ ((x <= &.0) /\ (y <= &.0) ))))`;
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[REAL_ARITH `((&.0 <. x) ==> (&.0 <=. x))`;REAL_ARITH `(&.0 <. x) ==> ~(x <=. &.0)`];
  EQ_TAC;
  ASM_MESON_TAC[REAL_PROP_NN_LCANCEL];
  ASM_MESON_TAC[REAL_LE_MUL;REAL_LT_IMP_LE];
  DISCH_TAC;
  DISJ_CASES_TAC (REAL_ARITH `(&.0 < x) \/ (x = &.0) \/ (x < &.0)`);
  ASM_MESON_TAC[];
  UND 1 THEN DISCH_THEN  DISJ_CASES_TAC;
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  ASM_SIMP_TAC[REAL_ARITH `((x <. &.0) ==> ~(&.0 <=. x))`;REAL_ARITH `(x <. &.0) ==> (x <=. &.0)`];
  USE 0 (SPECL [`--. (x:real)`;`--. (y:real)`]);
  UND 0;
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[REAL_ARITH `((x <. &.0) ==> ~(&.0 <=. x))`;REAL_ARITH `(x <. &.0) ==> (x <=. &.0)`];
  ]);;
  (* }}} *)

let ABS_SQUARE = prove_by_refinement(
  `!t u. abs(t) <. u ==> t*t <. u*u`,
  (* {{{ proof *)

  [
  REP_GEN_TAC;
  CONV_TAC (SUBS_CONV[SPEC `t:real` (REWRITE_RULE[POW_2] (GSYM REAL_POW2_ABS))]);
  ASSUME_TAC REAL_ABS_POS;
  USE 0 (SPEC `t:real`);
  ABBREV_TAC `(b:real) = (abs t)`;
  KILL 1;
  DISCH_ALL_TAC;
  MATCH_MP_TAC REAL_PROP_LT_LRMUL;
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let ABS_SQUARE_LE = prove_by_refinement(
  `!t u. abs(t) <=. u ==> t*t <=. u*u`,
  (* {{{ proof *)

  [
  REP_GEN_TAC;
  CONV_TAC (SUBS_CONV[SPEC `t:real` (REWRITE_RULE[POW_2] (GSYM REAL_POW2_ABS))]);
  ASSUME_TAC REAL_ABS_POS;
  USE 0 (SPEC `t:real`);
  ABBREV_TAC `(b:real) = (abs t)`;
  KILL 1;
  DISCH_ALL_TAC;
  MATCH_MP_TAC REAL_PROP_LE_LRMUL;
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let twopow_eps = prove_by_refinement(
  `!R e. ?n. (&.0 <. R)/\ (&.0 <. e) ==> R*(twopow(--: (&:n))) <. e`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  REWRITE_TAC[TWOPOW_NEG]; (* cs6b *)
  ASSUME_TAC (prove(`!n. &.0 < &.2 pow n`,REDUCE_TAC THEN ARITH_TAC));
  ONCE_REWRITE_TAC[REAL_MUL_AC];
  ASM_SIMP_TAC[REAL_INV_LT];
  ASM_SIMP_TAC[GSYM REAL_LT_LDIV_EQ];
  CONV_TAC (quant_right_CONV "n");
  DISCH_ALL_TAC;
  ASSUME_TAC (SPEC `R/e` REAL_ARCH_SIMPLE);
  CHO 3;
  EXISTS_TAC `n:num`;
  UND 3;
  MESON_TAC[POW_2_LT;REAL_LET_TRANS];
  ]);;

  (* }}} *)


(* ------------------------------------------------------------------ *)
(* finite products, in imitation of finite sums *)
(* ------------------------------------------------------------------ *)

let prod_EXISTS = prove_by_refinement(
  `?prod. (!f n.  prod(n,0) f = &1) /\
         (!f m n. prod(n,SUC m) f = prod(n,m) f * f(n + m))`,
(* {{{ proof *)
  [
  (CHOOSE_TAC o prove_recursive_functions_exist num_RECURSION) `(!f n. sm n 0 f = &1) /\ (!f m n. sm  n (SUC m) f = sm n m f * f(n + m))` ;
  EXISTS_TAC `\(n,m) f. (sm:num->num->(num->real)->real) n m f`;
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV) THEN ASM_REWRITE_TAC[]
  ]);;
(* }}} *)

let prod_DEF = new_specification ["prod"] prod_EXISTS;;

let prod = prove
 (`!n m. (prod(n,0) f = &1) /\
   (prod(n,SUC m) f = prod(n,m) f * f(n + m))`,
(* {{{ proof *)
  REWRITE_TAC[prod_DEF]);;
(* }}} *)

let PROD_TWO = prove_by_refinement(
 `!f n p. prod(0,n) f * prod(n,p) f = prod(0,n + p) f`,
(* {{{ proof *)
  [
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[prod; REAL_MUL_RID; MULT_CLAUSES;ADD_0];
  REWRITE_TAC[ARITH_RULE `n+| (SUC p) = (SUC (n+|p))`;prod;ARITH_RULE `0+|n = n`];
  ASM_REWRITE_TAC[REAL_MUL_ASSOC];
]);;
(* }}} *)


let ABS_PROD = prove_by_refinement(
 `!f m n. abs(prod(m,n) f) = prod(m,n) (\n. abs(f n))`,
(* {{{ proof *)
  [
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC;
  REWRITE_TAC[prod];
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[prod;ABS_MUL]
  ]);;
(* }}} *)

let PROD_EQ = prove_by_refinement
 (`!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (prod(m,n) f = prod(m,n) g)`,
(* {{{ proof *)

  [
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[prod];
  REWRITE_TAC[prod];
  DISCH_THEN (fun th -> MP_TAC th THEN (MP_TAC (SPEC `m+|n` th)));
  REWRITE_TAC[ARITH_RULE `(m<=| (m+|n))/\ (m +| n <| (SUC n +| m))`];
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  AP_THM_TAC THEN AP_TERM_TAC;
  FIRST_X_ASSUM MATCH_MP_TAC;
  GEN_TAC THEN DISCH_TAC;
  FIRST_X_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[ARITH_RULE `r <| (n+| m) ==> (r <| (SUC n +| m))`]
  ]);;

(* }}} *)

let PROD_POS = prove_by_refinement
 (`!f. (!n. &0 <= f(n)) ==> !m n. &0 <= prod(m,n) f`,
(* {{{ proof *)

  [
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[prod];
  REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_LE_MUL]
  ]);;
(* }}} *)

let PROD_POS_GEN = prove_by_refinement
 (`!f m n.
     (!n. m <= n ==> &0 <= f(n))
     ==> &0 <= prod(m,n) f`,
(* {{{ proof *)

  [
  REPEAT STRIP_TAC THEN SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THEN REWRITE_TAC[prod];
  REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_LE_MUL;ARITH_RULE `m <=| (m +| n)`]
  ]);;
(* }}} *)


let PROD_ABS = prove
 (`!f m n. abs(prod(m,n) (\m. abs(f m))) = prod(m,n) (\m. abs(f m))`,
(* {{{ proof *)
  REWRITE_TAC[ABS_PROD;REAL_ARITH `||. (||. x) = (||. x)`]);;
(* }}} *)

let PROD_ZERO = prove_by_refinement
 (`!f m n. (?p. (m <= p /\ (p < (n+| m)) /\ (f p = (&.0)))) ==>
         (prod(m,n) f = &0)`,
(* {{{ proof *)
  [
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN (REWRITE_TAC[prod]);
  ARITH_TAC;
  DISCH_THEN CHOOSE_TAC;
  ASM_CASES_TAC `p <| (n+| m)`;
  MATCH_MP_TAC (prove (`(x = (&.0)) ==> (x *. y = (&.0))`,(DISCH_THEN (fun th -> (REWRITE_TAC[th]))) THEN REAL_ARITH_TAC));
  FIRST_X_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[];
  POP_ASSUM (fun th -> ASSUME_TAC (MATCH_MP (ARITH_RULE `(~(p <| (n+|m)) ==> ((p <| ((SUC n) +| m)) ==> (p = ((m +| n)))))`) th));
  MATCH_MP_TAC (prove (`(x = (&.0)) ==> (y *. x = (&.0))`,(DISCH_THEN (fun th -> (REWRITE_TAC[th]))) THEN REAL_ARITH_TAC));
  ASM_MESON_TAC[]
 ]);;
(* }}} *)

let PROD_MUL = prove_by_refinement(
  `!f g m n. prod(m,n) (\n. f(n) * g(n)) = prod(m,n) f * prod(m,n) g`,
  (* {{{ proof *)
  [
  EVERY(replicate GEN_TAC 3) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[prod];
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_AC];
  ]);;
  (* }}} *)

let PROD_CMUL = prove_by_refinement(
  `!f c m n. prod(m,n) (\n. c * f(n)) = (c **. n) * prod(m,n) f`,
  (* {{{ proof *)
  [
  EVERY(replicate GEN_TAC 3) THEN INDUCT_TAC THEN ASM_REWRITE_TAC[prod;pow];
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_AC];
  ]);;
  (* }}} *)

(* ------------------------------------------------------------------ *)
(*  LEMMAS ABOUT SETS                                                 *)
(* ------------------------------------------------------------------ *)

(* IN_ELIM_THM produces garbled results at times. I like this better: *)

(*** JRH replaced this with the "new" IN_ELIM_THM; see how it works.

let IN_ELIM_THM' = prove_by_refinement(
 `(!P. !x:A. x IN (GSPEC P) <=> P x) /\
   (!P. !x:A. x IN (\x. P x) <=> P x) /\
   (!P. !x:A. (GSPEC P) x <=> P x) /\
   (!P (x:A) (t:A). (\t. (?y:A. P y /\ (t = y))) x <=> P x)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[IN; GSPEC];
  MESON_TAC[];
  ]);;
  (* }}} *)

 ****)

let IN_ELIM_THM' = IN_ELIM_THM;;

let SURJ_IMAGE = prove_by_refinement(
  `!(f:A->B) a b. SURJ f a b ==> (b = (IMAGE f a))`,
(* {{{ proof *)

  [
  REPEAT GEN_TAC;
  REWRITE_TAC[SURJ;IMAGE];
  DISCH_ALL_TAC;
  REWRITE_TAC[EXTENSION];
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM];
  ASM_MESON_TAC[]]

(* }}} *)
);;


let SURJ_FINITE = prove_by_refinement(
  `!a b (f:A->B). FINITE a /\ (SURJ f a b) ==> FINITE b`,
(* {{{ *)

  [
  ASM_MESON_TAC[SURJ_IMAGE;FINITE_IMAGE]
  ]);;

(* }}} *)

let BIJ_INVERSE = prove_by_refinement(
  `!a b (f:A->B). (SURJ f a b) ==> (?(g:B->A). (INJ g b a))`,
(* {{{ proof *)

  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_THEN `!y. ?u. ((y IN b) ==> ((u IN a) /\ ((f:A->B) u = y)))` ASSUME_TAC;
  ASM_MESON_TAC[SURJ];
  LABEL_ALL_TAC;
  H_REWRITE_RULE[THM SKOLEM_THM] (HYP "1");
  LABEL_ALL_TAC;
  H_UNDISCH_TAC (HYP"2");
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `u:B->A`;
  REWRITE_TAC[INJ] THEN  CONJ_TAC THEN (ASM_MESON_TAC[])
  ]

(* }}} *)
);;

(* complement of an intersection is a union of complements *)
let UNIONS_INTERS = prove_by_refinement(
  `!(X:A->bool)  V.
     (X DIFF (INTERS V) = UNIONS (IMAGE ((DIFF) X) V))`,
(* {{{ proof *)

  [
  REPEAT GEN_TAC;
  MATCH_MP_TAC SUBSET_ANTISYM;
  CONJ_TAC;
  REWRITE_TAC[SUBSET;IMAGE;IN_ELIM_THM];
  X_GEN_TAC `c:A`;
  REWRITE_TAC[IN_DIFF;IN_INTERS;IN_UNIONS;NOT_FORALL_THM];
  DISCH_ALL_TAC;
  UNDISCH_FIND_THEN `(?)` CHOOSE_TAC;
  EXISTS_TAC `(X DIFF t):A->bool`;
  REWRITE_TAC[IN_ELIM_THM];
  CONJ_TAC;
  EXISTS_TAC `t:A->bool`;
  ASM_MESON_TAC[];
  REWRITE_TAC[IN_DIFF];
  ASM_MESON_TAC[];
  REWRITE_TAC[SUBSET;IMAGE;IN_ELIM_THM];
  X_GEN_TAC `c:A`;
  REWRITE_TAC[IN_DIFF;IN_UNIONS];
  DISCH_THEN CHOOSE_TAC;
  UNDISCH_FIND_TAC `(IN)`;
  REWRITE_TAC[IN_INTERS;IN_ELIM_THM];
  DISCH_ALL_TAC;
  UNDISCH_FIND_THEN `(?)` CHOOSE_TAC;
  CONJ_TAC;
  ASM_MESON_TAC[SUBSET_DIFF;SUBSET];
  REWRITE_TAC[NOT_FORALL_THM];
  EXISTS_TAC `x:A->bool`;
  ASM_MESON_TAC[IN_DIFF];
  ]);;

(* }}} *)

let INTERS_SUBSET = prove_by_refinement (
   `!X (A:A->bool).  (A IN X) ==> (INTERS X SUBSET A)`,
(* {{{ *)
  [
  REPEAT GEN_TAC;
  REWRITE_TAC[SUBSET;IN_INTERS];
  MESON_TAC[IN];
  ]);;
(* }}} *)

let sub_union = prove_by_refinement(
  `!X (U:(A->bool)->bool). (U X) ==> (X SUBSET (UNIONS U))`,
(* {{{ *)
 [
 DISCH_ALL_TAC;
 REWRITE_TAC[SUBSET;IN_ELIM_THM;UNIONS];
 REWRITE_TAC[IN];
 DISCH_ALL_TAC;
 EXISTS_TAC `X:A->bool`;
 ASM_REWRITE_TAC[];
 ]);;
(* }}} *)

let IMAGE_SURJ = prove_by_refinement(
 `!(f:A->B) a. SURJ f a (IMAGE f a)`,
(* {{{ *)
 [
 REWRITE_TAC[SURJ;IMAGE;IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)

let SUBSET_PREIMAGE = prove_by_refinement(
  `!(f:A->B) X Y. (Y SUBSET (IMAGE f X)) ==>
    (?Z. (Z SUBSET X) /\ (Y = IMAGE f Z))`,
(* {{{ proof *)
 [
 DISCH_ALL_TAC;
 EXISTS_TAC `{x | (x IN (X:A->bool))/\ (f x IN (Y:B->bool)) }`;
 CONJ_TAC;
 REWRITE_TAC[SUBSET;IN_ELIM_THM];
 MESON_TAC[];
 REWRITE_TAC[EXTENSION];
 X_GEN_TAC `y:B`;
 UNDISCH_FIND_TAC `(SUBSET)`;
 REWRITE_TAC[SUBSET;IN_IMAGE];
 REWRITE_TAC[IN_ELIM_THM];
 DISCH_THEN (fun t-> MP_TAC (SPEC `y:B` t));
 MESON_TAC[];
 ]);;
(* }}} *)

let UNIONS_INTER = prove_by_refinement(
  `!(U:(A->bool)->bool) A. (((UNIONS U) INTER A) =
       (UNIONS (IMAGE ((INTER) A) U)))`,
 (* {{{ proof *)
 [
 REPEAT GEN_TAC;
 MATCH_MP_TAC (prove(`((C SUBSET (B:A->bool)) /\ (C SUBSET A) /\ ((A INTER B) SUBSET C)) ==> ((B INTER A) = C)`,SET_TAC[]));
 CONJ_TAC;
 REWRITE_TAC[SUBSET;UNIONS;IN_ELIM_THM];
 REWRITE_TAC[IN_IMAGE];
 SET_TAC[];
 REWRITE_TAC[SUBSET;UNIONS;IN_IMAGE];
 CONJ_TAC;
 REWRITE_TAC[IN_ELIM_THM];
 X_GEN_TAC `y:A`;
 DISCH_THEN CHOOSE_TAC;
 ASM_MESON_TAC[IN_INTER];
 REWRITE_TAC[IN_INTER];
 REWRITE_TAC[IN_ELIM_THM];
 X_GEN_TAC `y:A`;
 DISCH_ALL_TAC;
 UNDISCH_FIND_THEN `(?)` CHOOSE_TAC;
 EXISTS_TAC `A INTER (u:A->bool)`;
 ASM SET_TAC[];
 ]);;
(* }}} *)

let UNIONS_SUBSET = prove_by_refinement(
 `!U (X:A->bool). (!A. (A IN U) ==> (A SUBSET X))  ==> (UNIONS U SUBSET X)`,
(* {{{ *)
 [
 REPEAT GEN_TAC;
 SET_TAC[];
 ]);;
(* }}} *)

let SUBSET_INTER = prove_by_refinement(
 `!X A (B:A->bool). (X SUBSET (A INTER B)) <=> (X SUBSET A) /\ (X SUBSET B)`,
(* {{{ *)
 [
 REWRITE_TAC[SUBSET;INTER;IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)

let EMPTY_EXISTS = prove_by_refinement(
 `!X. ~(X = {}) <=> (? (u:A). (u IN X))`,
(* {{{ *)
 [
 REWRITE_TAC[EXTENSION];
 REWRITE_TAC[IN;EMPTY];
 MESON_TAC[];
 ]);;
(* }}} *)

let UNIONS_UNIONS = prove_by_refinement(
 `!A B. (A SUBSET B) ==>(UNIONS (A:(A->bool)->bool) SUBSET (UNIONS B))`,
(* {{{ *)
 [
 REWRITE_TAC[SUBSET;UNIONS;IN_ELIM_THM];
 MESON_TAC[IN];
 ]);;
(* }}} *)


(* nested union can flatten from outside in, or inside out *)
let UNIONS_IMAGE_UNIONS = prove_by_refinement(
  `!(X:((A->bool)->bool)->bool).
    UNIONS (UNIONS X) = (UNIONS (IMAGE UNIONS X))`,
 (* {{{ proof *)
  [
  GEN_TAC;
  REWRITE_TAC[EXTENSION;IN_UNIONS];
  GEN_TAC;
  REWRITE_TAC[EXTENSION;IN_UNIONS];
  EQ_TAC;
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  DISCH_ALL_TAC;
  FIRST_ASSUM MP_TAC;
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `UNIONS (t':(A->bool)->bool)`;
  REWRITE_TAC[IN_UNIONS;IN_IMAGE];
  CONJ_TAC;
  EXISTS_TAC `(t':(A->bool)->bool)`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  DISCH_THEN CHOOSE_TAC;
  FIRST_ASSUM MP_TAC;
  REWRITE_TAC[IN_IMAGE];
  DISCH_ALL_TAC;
  FIRST_ASSUM MP_TAC;
  DISCH_THEN CHOOSE_TAC;
  UNDISCH_TAC `(x:A) IN t`;
  FIRST_ASSUM (fun t-> REWRITE_TAC[t]);
  REWRITE_TAC[IN_UNIONS];
  DISCH_THEN (CHOOSE_TAC);
  EXISTS_TAC `t':(A->bool)`;
  CONJ_TAC;
  EXISTS_TAC `x':(A->bool)->bool`;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  ]);;
(* }}} *)


let INTERS_SUBSET2 = prove_by_refinement(
  `!X A. (?(x:A->bool). (A x /\ (x SUBSET X))) ==> ((INTERS A) SUBSET X)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[SUBSET;INTERS;IN_ELIM_THM'];
  REWRITE_TAC[IN];
  MESON_TAC[];
  ]);;
  (* }}} *)

(**** New proof by JRH; old one breaks because of new set comprehensions

let INTERS_EMPTY = prove_by_refinement(
  `INTERS EMPTY = (UNIV:A->bool)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[INTERS;NOT_IN_EMPTY;IN_ELIM_THM';];
  REWRITE_TAC[UNIV;GSPEC];
  MATCH_MP_TAC  EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  MESON_TAC[];
  ]);;
  (* }}} *)

 ****)

let INTERS_EMPTY = prove_by_refinement(
  `INTERS EMPTY = (UNIV:A->bool)`,
  [SET_TAC[]]);;

let preimage = new_definition `preimage dom (f:A->B)
  Z = {x | (x IN dom) /\ (f x IN Z)}`;;

let in_preimage = prove_by_refinement(
  `!f x Z dom. x IN (preimage dom (f:A->B) Z) <=> (x IN dom) /\ (f x IN Z)`,
(* {{{ *)
  [
  REWRITE_TAC[preimage];
  REWRITE_TAC[IN_ELIM_THM']
  ]);;
(* }}} *)

(* Partial functions, which we identify with functions that
   take the canonical choice of element outside the domain. *)

let supp = new_definition
  `supp (f:A->B) = \ x.  ~(f x = (CHOICE (UNIV:B ->bool)) )`;;

let func = new_definition
  `func a b = (\ (f:A->B). ((!x. (x IN a) ==> (f x IN b)) /\
              ((supp f) SUBSET a))) `;;


(* relations *)
let reflexive = new_definition
  `reflexive (f:A->A->bool) <=> (!x. f x x)`;;

let symmetric = new_definition
  `symmetric (f:A->A->bool) <=> (!x y. f x y ==> f y x)`;;

let transitive = new_definition
  `transitive (f:A->A->bool) <=> (!x y z. f x y /\ f y z ==> f x z)`;;

let equivalence_relation = new_definition
  `equivalence_relation (f:A->A->bool) <=>
    (reflexive f) /\ (symmetric f) /\ (transitive f)`;;

(* We do not introduce the equivalence class of f explicitly, because
   it is represented directly in HOL by (f a) *)

let partition_DEF = new_definition
  `partition (A:A->bool) SA <=> (UNIONS SA = A) /\
   (!a b. ((a IN SA) /\ (b IN SA) /\ (~(a = b)) ==> ({} = (a INTER b))))`;;

let DIFF_DIFF2 = prove_by_refinement(
  `!X (A:A->bool). (A SUBSET X) ==> ((X DIFF (X DIFF A)) = A)`,
  [
  SET_TAC[]
  ]);;

(*** Old proof replaced by JRH: no longer UNWIND_THM[12] clause in IN_ELIM_THM

let GSPEC_THM = prove_by_refinement(
  `!P (x:A). (?y. P y /\ (x = y)) <=> P x`,
  [REWRITE_TAC[IN_ELIM_THM]]);;

***)

let GSPEC_THM = prove_by_refinement(
  `!P (x:A). (?y. P y /\ (x = y)) <=> P x`,
  [MESON_TAC[]]);;

let CARD_GE_REFL = prove
 (`!s:A->bool. s >=_c s`,
  GEN_TAC THEN REWRITE_TAC[GE_C] THEN
  EXISTS_TAC `\x:A. x` THEN MESON_TAC[]);;

let FINITE_HAS_SIZE_LEMMA = prove
 (`!s:A->bool. FINITE s ==> ?n:num. {x | x < n} >=_c s`,
  MATCH_MP_TAC FINITE_INDUCT THEN CONJ_TAC THENL
   [EXISTS_TAC `0` THEN REWRITE_TAC[NOT_IN_EMPTY; GE_C; IN_ELIM_THM];
    REPEAT GEN_TAC THEN DISCH_THEN(X_CHOOSE_TAC `N:num`) THEN
    EXISTS_TAC `SUC N` THEN POP_ASSUM MP_TAC THEN PURE_REWRITE_TAC[GE_C] THEN
    DISCH_THEN(X_CHOOSE_TAC `f:num->A`) THEN
    EXISTS_TAC `\n:num. if n = N then x:A else f n` THEN
    X_GEN_TAC `y:A` THEN PURE_REWRITE_TAC[IN_INSERT] THEN
    DISCH_THEN(DISJ_CASES_THEN2 SUBST_ALL_TAC (ANTE_RES_THEN MP_TAC)) THENL
     [EXISTS_TAC `N:num` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN ARITH_TAC;
      DISCH_THEN(X_CHOOSE_THEN `n:num` MP_TAC) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `n:num < N` THEN COND_CASES_TAC THEN
      ASM_REWRITE_TAC[LT_REFL] THEN ARITH_TAC]]);;

let NUM_COUNTABLE = prove_by_refinement(
  `COUNTABLE (UNIV:num->bool)`,
  (* {{{ proof *)

  [
  REWRITE_TAC[COUNTABLE;CARD_GE_REFL];
  ]);;

  (* }}} *)

let NUM2_COUNTABLE = prove_by_refinement(
  `COUNTABLE {((x:num),(y:num)) | T}`,
  (* {{{ proof *)
  [
  CHOOSE_TAC (ISPECL[`(0,0)`;`(\ (a:num,b:num) (n:num) . if (b=0) then (0,a+b+1) else (a+1,b-1))`] num_RECURSION);
  REWRITE_TAC[COUNTABLE;GE_C;IN_ELIM_THM'];
  NAME_CONFLICT_TAC;
  EXISTS_TAC `fn:num -> (num#num)`;
  X_GEN_TAC `p:num#num`;
  REPEAT (DISCH_THEN (CHOOSE_THEN MP_TAC));
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  REWRITE_TAC[IN_UNIV];
  SUBGOAL_TAC `?t. t = x+|y'`;
  MESON_TAC[];
  SPEC_TAC (`x:num`,`a:num`);
  SPEC_TAC (`y':num`,`b:num`);
  CONV_TAC (quant_left_CONV "t");
  CONV_TAC (quant_left_CONV "t");
  CONV_TAC (quant_left_CONV "t");
  INDUCT_TAC;
  REDUCE_TAC;
  REP_GEN_TAC;
  DISCH_THEN (fun t -> REWRITE_TAC[t]);
  EXISTS_TAC `0`;
  ASM_REWRITE_TAC[];
  CONV_TAC (quant_left_CONV "a");
  INDUCT_TAC;
  REDUCE_TAC;
  GEN_TAC;
  USE 1 (SPECL [`0`;`t:num`]);
  UND 1 THEN REDUCE_TAC;
  DISCH_THEN (X_CHOOSE_TAC `n:num`);
  AND 0;
  USE 0 (SPEC `n:num`);
  UND 0;
  UND 1;
  DISCH_THEN (fun t-> REWRITE_TAC[GSYM t]);
  CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV);
  BETA_TAC;
  REDUCE_TAC;
  DISCH_ALL_TAC;
  EXISTS_TAC `SUC n`;
  EXPAND_TAC "b";
  KILL 0;
  ASM_REWRITE_TAC[];
  REWRITE_TAC [ARITH_RULE `SUC t = t+|1`];
  GEN_TAC;
  ABBREV_TAC `t'  = SUC t`;
  USE 2 (SPEC `SUC b`);
  DISCH_TAC;
  UND 2;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[ARITH_RULE `SUC a +| b = a +| SUC b`];
  DISCH_THEN (X_CHOOSE_TAC `n:num`);
  EXISTS_TAC `SUC n`;
  AND 0;
  USE 0 (SPEC `n:num`);
  UND 0;
  UND 2;
  DISCH_THEN (fun t->REWRITE_TAC[GSYM t]);
  CONV_TAC (ONCE_DEPTH_CONV GEN_BETA_CONV);
  BETA_TAC;
  REDUCE_TAC;
  DISCH_THEN (fun t->REWRITE_TAC[t]);
  REWRITE_TAC[ARITH_RULE `SUC a = a+| 1`];
  ]);;
  (* }}} *)

let COUNTABLE_UNIONS = prove_by_refinement(
  `!A:(A->bool)->bool. (COUNTABLE A) /\
      (!a. (a IN A) ==> (COUNTABLE a)) ==> (COUNTABLE (UNIONS A))`,
  (* {{{ proof *)
  [
  GEN_TAC;
  DISCH_ALL_TAC;
  USE 0 (REWRITE_RULE[COUNTABLE;GE_C;IN_UNIV]);
  CHO 0;
  USE 0 (CONV_RULE (quant_left_CONV "x"));
  USE 0 (CONV_RULE (quant_left_CONV "x"));
  CHO 0;
  USE 1 (REWRITE_RULE[COUNTABLE;GE_C;IN_UNIV]);
  USE 1 (CONV_RULE (quant_left_CONV "f"));
  USE 1 (CONV_RULE (quant_left_CONV "f"));
  UND 1;
  DISCH_THEN (X_CHOOSE_TAC `g:(A->bool)->num->A`);
  SUBGOAL_TAC `!a y. (a IN (A:(A->bool)->bool)) /\ (y IN a) ==> (? (u:num) (v:num). ( a = f u) /\ (y = g a v))`;
  REP_GEN_TAC;
  DISCH_ALL_TAC;
  USE 1 (SPEC `a:A->bool`);
  USE 0 (SPEC `a:A->bool`);
  EXISTS_TAC `(x:(A->bool)->num) a`;
  ASM_SIMP_TAC[];
  ASSUME_TAC NUM2_COUNTABLE;
  USE 2 (REWRITE_RULE[COUNTABLE;GE_C;IN_ELIM_THM';IN_UNIV]);
  USE 2 (CONV_RULE NAME_CONFLICT_CONV);
  UND 2 THEN (DISCH_THEN (X_CHOOSE_TAC `h:num->(num#num)`));
  DISCH_TAC;
  REWRITE_TAC[COUNTABLE;GE_C;IN_ELIM_THM';IN_UNIV;IN_UNIONS];
  EXISTS_TAC `(\p. (g:(A->bool)->num->A) ((f:num->(A->bool)) (FST ((h:num->(num#num)) p))) (SND (h p)))`;
  BETA_TAC;
  GEN_TAC;
  DISCH_THEN (CHOOSE_THEN MP_TAC);
  DISCH_ALL_TAC;
  USE 3 (SPEC `t:A->bool`);
  USE 3 (SPEC `y:A`);
  UND 3 THEN (ASM_REWRITE_TAC[]);
  REPEAT (DISCH_THEN(CHOOSE_THEN (MP_TAC)));
  DISCH_ALL_TAC;
  USE 2 (SPEC `(u:num,v:num)`);
  SUBGOAL_TAC `?x' y'. (u:num,v:num) = (x',y')`;
  MESON_TAC[];
  DISCH_TAC;
  UND 2;
  ASM_REWRITE_TAC[];
  DISCH_THEN (CHOOSE_THEN (ASSUME_TAC o GSYM));
  EXISTS_TAC `x':num`;
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let COUNTABLE_IMAGE = prove_by_refinement(
  `!(A:A->bool) (B:B->bool) . (COUNTABLE A) /\ (?f. (B SUBSET IMAGE f A)) ==>
        (COUNTABLE B)`,
  (* {{{ proof *)
  [
  REWRITE_TAC[COUNTABLE;GE_C;IN_UNIV;IN_ELIM_THM';SUBSET];
  DISCH_ALL_TAC;
  CHO 0;
  USE 1 (REWRITE_RULE[IMAGE;IN_ELIM_THM']);
  CHO 1;
  USE 1 (REWRITE_RULE[IN_ELIM_THM']);
  USE 1 (CONV_RULE NAME_CONFLICT_CONV);
  EXISTS_TAC `(f':A->B) o (f:num->A)`;
  REWRITE_TAC[o_DEF];
  DISCH_ALL_TAC;
  USE 1 (SPEC `y:B`);
  UND 1;
  ASM_REWRITE_TAC[];
  DISCH_THEN CHOOSE_TAC;
  USE 0 (SPEC `x':A`);
  UND 0 THEN (ASM_REWRITE_TAC[]) THEN DISCH_TAC;
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

let COUNTABLE_CARD = prove_by_refinement(
  `!(A:A->bool) (B:B->bool). (COUNTABLE A) /\ (A >=_c B) ==>
     (COUNTABLE B)`,
  (* {{{ proof *)

  [
  DISCH_ALL_TAC;
  MATCH_MP_TAC COUNTABLE_IMAGE;
  EXISTS_TAC `A:A->bool`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[IMAGE;SUBSET;IN_ELIM_THM'];
  USE 1 (REWRITE_RULE[GE_C]);
  CHO 1;
  EXISTS_TAC `f:A->B`;
  ASM_REWRITE_TAC[];
  ]);;

  (* }}} *)

let COUNTABLE_NUMSEG = prove_by_refinement(
  `!n. COUNTABLE {x | x <| n}`,
  (* {{{ proof *)
  [
  GEN_TAC;
  REWRITE_TAC[COUNTABLE;GE_C;IN_UNIV];
  EXISTS_TAC `I:num->num`;
  REDUCE_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  MESON_TAC[];
  ]);;
  (* }}} *)

let FINITE_COUNTABLE = prove_by_refinement(
  `!(A:A->bool). (FINITE A) ==> (COUNTABLE A)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  USE 0 (MATCH_MP FINITE_HAS_SIZE_LEMMA);
  CHO 0;
  ASSUME_TAC(SPEC `n:num` COUNTABLE_NUMSEG);
  JOIN 1 0;
  USE 0 (MATCH_MP COUNTABLE_CARD);
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let num_infinite = prove_by_refinement(
  `~ (FINITE (UNIV:num->bool))`,
  (* {{{ proof *)
  [
  PROOF_BY_CONTR_TAC;
  USE 0 (REWRITE_RULE[]);
  USE 0 (MATCH_MP num_FINITE_AVOID);
  USE 0 (REWRITE_RULE[IN_UNIV]);
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let num_SEG_UNION = prove_by_refinement(
  `!i. ({u | i <| u} UNION {m | m <=| i}) = UNIV`,
  (* {{{ proof *)
  [
  REP_BASIC_TAC;
  SUBGOAL_TAC `({u | i <| u} UNION {m | m <=| i}) = UNIV`;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[UNIV;UNION;IN_ELIM_THM'];
  ARITH_TAC;
  REWRITE_TAC[];
  ]);;
  (* }}} *)

let num_above_infinite = prove_by_refinement(
  `!i. ~ (FINITE {u | i <| u})`,
  (* {{{ proof *)
  [
  GEN_TAC;
  PROOF_BY_CONTR_TAC;
  USE 0 (REWRITE_RULE[]);
  ASSUME_TAC(SPEC `i:num` FINITE_NUMSEG_LE);
  JOIN 0 1;
  USE 0 (MATCH_MP FINITE_UNION_IMP);
  SUBGOAL_TAC `({u | i <| u} UNION {m | m <=| i}) = UNIV`;
  REWRITE_TAC[num_SEG_UNION];
  DISCH_TAC;
  UND 0;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[num_infinite];
  ]);;
  (* }}} *)

let INTER_FINITE = prove_by_refinement(
  `!s (t:A->bool). (FINITE s ==> FINITE(s INTER t)) /\ (FINITE t ==> FINITE (s INTER t))`,
  (* {{{ proof *)

  [
  CONV_TAC (quant_right_CONV "t");
  CONV_TAC (quant_right_CONV "s");
  SUBCONJ_TAC;
  DISCH_ALL_TAC;
  SUBGOAL_TAC `s INTER t SUBSET (s:A->bool)`;
  SET_TAC[];
  ASM_MESON_TAC[FINITE_SUBSET];
  MESON_TAC[INTER_COMM];
  ]);;

  (* }}} *)

let num_above_finite = prove_by_refinement(
  `!i J. (FINITE (J INTER {u | (i <| u)})) ==> (FINITE J)`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  SUBGOAL_TAC `J = (J INTER {u | (i <| u)}) UNION (J INTER {m | m <=| i})`;
  REWRITE_TAC[GSYM UNION_OVER_INTER;num_SEG_UNION;INTER_UNIV];
  DISCH_TAC;
  ASM (ONCE_REWRITE_TAC)[];
  REWRITE_TAC[FINITE_UNION];
  ASM_REWRITE_TAC[];
  MP_TAC (SPEC `i:num` FINITE_NUMSEG_LE);
  REWRITE_TAC[INTER_FINITE];
  ]);;
  (* }}} *)

let SUBSET_SUC = prove_by_refinement(
  `!(f:num->A->bool). (!i. f i SUBSET f (SUC i)) ==> (! i j. ( i <=| j) ==> (f i SUBSET f j))`,
  (* {{{ proof *)
  [
  GEN_TAC;
  DISCH_TAC;
  REP_GEN_TAC;
  MP_TAC (prove( `?n. n = j -| i`,MESON_TAC[]));
  CONV_TAC (quant_left_CONV "n");
  SPEC_TAC (`i:num`,`i:num`);
  SPEC_TAC (`j:num`,`j:num`);
  REP 2(  CONV_TAC (quant_left_CONV "n"));
  INDUCT_TAC;
  REP_GEN_TAC;
  DISCH_ALL_TAC;
  JOIN 1 2;
  USE 1 (CONV_RULE REDUCE_CONV);
  ASM_REWRITE_TAC[SUBSET];
  REP_GEN_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `?j'. j = SUC j'`;
  DISJ_CASES_TAC (SPEC `j:num` num_CASES);
  UND 2;
  ASM_REWRITE_TAC[];
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  DISCH_THEN CHOOSE_TAC;
  ASM_REWRITE_TAC[];
  USE 0 (SPEC `j':num`);
  USE 1(SPECL [`j':num`;`i:num`]);
  DISCH_TAC;
  SUBGOAL_TAC `(n = j'-|i)`;
  UND 2;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `(i<=| j')`;
  USE 2 (MATCH_MP(ARITH_RULE `(SUC n = j -| i) ==> (0 < j -| i)`));
  UND 2;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  UND 1;
  ASM_REWRITE_TAC [];
  DISCH_ALL_TAC;
  REWR 6;
  ASM_MESON_TAC[SUBSET_TRANS];
  ]);;
  (* }}} *)

let SUBSET_SUC2 = prove_by_refinement(
  `!(f:num->A->bool). (!i. f (SUC i) SUBSET (f i)) ==> (! i j. ( i <=| j) ==> (f j SUBSET f i))`,
  (* {{{ proof *)
  [
  GEN_TAC;
  DISCH_TAC;
  REP_GEN_TAC;
  MP_TAC (prove( `?n. n = j -| i`,MESON_TAC[]));
  CONV_TAC (quant_left_CONV "n");
  SPEC_TAC (`i:num`,`i:num`);
  SPEC_TAC (`j:num`,`j:num`);
  REP 2(  CONV_TAC (quant_left_CONV "n"));
  INDUCT_TAC;
  REP_GEN_TAC;
  DISCH_ALL_TAC;
  JOIN 1 2;
  USE 1 (CONV_RULE REDUCE_CONV);
  ASM_REWRITE_TAC[SUBSET];
  REP_GEN_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `?j'. j = SUC j'`;
  DISJ_CASES_TAC (SPEC `j:num` num_CASES);
  UND 2;
  ASM_REWRITE_TAC[];
  REDUCE_TAC;
  ASM_REWRITE_TAC[];
  DISCH_THEN CHOOSE_TAC;
  ASM_REWRITE_TAC[];
  USE 0 (SPEC `j':num`);
  USE 1(SPECL [`j':num`;`i:num`]);
  DISCH_TAC;
  SUBGOAL_TAC `(n = j'-|i)`;
  UND 2;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  DISCH_TAC;
  SUBGOAL_TAC `(i<=| j')`;
  USE 2 (MATCH_MP(ARITH_RULE `(SUC n = j -| i) ==> (0 < j -| i)`));
  UND 2;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  UND 1;
  ASM_REWRITE_TAC [];
  DISCH_ALL_TAC;
  REWR 6;
  ASM_MESON_TAC[SUBSET_TRANS];
  ]);;
  (* }}} *)

let INFINITE_PIGEONHOLE = prove_by_refinement(
  `!I (f:A->B) B C. (~(FINITE {i | (I i) /\ (C (f i))})) /\ (FINITE B) /\
    (C SUBSET (UNIONS B)) ==>
    (?b. (B b) /\ ~(FINITE {i | (I i) /\ (C INTER b) (f i) }))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  PROOF_BY_CONTR_TAC;
  USE 3 (  CONV_RULE (quant_left_CONV "b"));
  UND 0;
  TAUT_TAC `P ==> (~P ==> F)`;
  SUBGOAL_TAC `{i | I' i /\ (C ((f:A->B) i))} = UNIONS (IMAGE (\b. {i | I' i /\ ((C INTER b) (f i))}) B)`;
  REWRITE_TAC[UNIONS;IN_IMAGE];
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  REWRITE_TAC[IN_ELIM_THM'];
  ABBREV_TAC `j = (x:A)`;
  EQ_TAC;
  DISCH_ALL_TAC;
  USE 2 (REWRITE_RULE [SUBSET;UNIONS]);
  USE 2 (REWRITE_RULE[IN_ELIM_THM']);
  USE 2 (SPEC `(f:A->B) j`);
  USE 2 (REWRITE_RULE[IN]);
  REWR 2;
  CHO 2;
  CONV_TAC (quant_left_CONV "x");
  CONV_TAC (quant_left_CONV "x");
  EXISTS_TAC (`u:B->bool`);
  NAME_CONFLICT_TAC;
  EXISTS_TAC (`{i' | I' i' /\ (C INTER u) ((f:A->B) i')}`);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[IN_ELIM_THM';INTER];
  REWRITE_TAC[IN];
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  CHO 4;
  AND 4;
  CHO 5;
  REWR 4;
  USE 4 (REWRITE_RULE[IN_ELIM_THM';INTER]);
  USE 4 (REWRITE_RULE[IN]);
  ASM_REWRITE_TAC[];
  DISCH_TAC;
  ASM_REWRITE_TAC[];
  SUBGOAL_TAC `FINITE (IMAGE (\b. {i | I' i /\ (C INTER b) ((f:A->B) i)}) B)`;
  MATCH_MP_TAC FINITE_IMAGE;
  ASM_REWRITE_TAC[];
  SIMP_TAC[FINITE_UNIONS];
  DISCH_TAC;
  GEN_TAC;
  REWRITE_TAC[IN_IMAGE];
  DISCH_THEN (X_CHOOSE_TAC `b:B->bool`);
  ASM_REWRITE_TAC[];
  USE 3 (SPEC `b:B->bool`);
  UND 3;
  AND 5;
  UND 3;
  ABBREV_TAC `r = {i | I' i /\ (C INTER b) ((f:A->B) i)}`;
  MESON_TAC[IN];
  ]);;
  (* }}} *)

let real_FINITE = prove_by_refinement(
  `!(s:real->bool). FINITE s ==> (?a. !x. x IN s ==> (x <=. a))`,
  (* {{{ proof *)
  [
  DISCH_ALL_TAC;
  ASSUME_TAC REAL_ARCH_SIMPLE;
  USE 1 (CONV_RULE (quant_left_CONV "n"));
  CHO 1;
  SUBGOAL_TAC `FINITE (IMAGE (n:real->num) s)`;
  ASM_MESON_TAC[FINITE_IMAGE];
(*** JRH -- num_FINITE is now an equivalence not an implication
  ASSUME_TAC (SPEC `IMAGE (n:real->num) s` num_FINITE);
 ***)
  ASSUME_TAC(fst(EQ_IMP_RULE(SPEC `IMAGE (n:real->num) s` num_FINITE)));
  DISCH_TAC;
  REWR 2;
  CHO 2;
  USE 2 (REWRITE_RULE[IN_IMAGE]);
  USE 2 (CONV_RULE NAME_CONFLICT_CONV);
  EXISTS_TAC `&.a`;
  GEN_TAC;
  USE 2 (CONV_RULE (quant_left_CONV "x'"));
  USE 2 (CONV_RULE (quant_left_CONV "x'"));
  USE 2 (SPEC `x:real`);
  USE 2 (SPEC `(n:real->num) x`);
  DISCH_TAC;
  REWR 2;
  USE 1 (SPEC `x:real`);
  UND 1;
  MATCH_MP_TAC (REAL_ARITH `a<=b ==> ((x <= a) ==> (x <=. b))`);
  REDUCE_TAC;
  ASM_REWRITE_TAC [];
  ]);;
  (* }}} *)

let UNIONS_DELETE = prove_by_refinement(
  `!s. (UNIONS (s:(A->bool)->bool)) = (UNIONS (s DELETE (EMPTY)))`,
  (* {{{ proof *)
  [
  REWRITE_TAC[UNIONS;DELETE;EMPTY];
  GEN_TAC;
  MATCH_MP_TAC EQ_EXT;
  REWRITE_TAC[IN_ELIM_THM'];
  GEN_TAC;
  REWRITE_TAC[IN];
  MESON_TAC[];
  ]);;
  (* }}} *)


(* ------------------------------------------------------------------ *)
(* Partial functions, which we identify with functions that
   take the canonical choice of element outside the domain. *)
(* ------------------------------------------------------------------ *)

let SUPP = new_definition
  `SUPP (f:A->B) = \ x.  ~(f x = (CHOICE (UNIV:B ->bool)) )`;;

let FUN = new_definition
  `FUN a b = (\ (f:A->B). ((!x. (x IN a) ==> (f x IN b)) /\
              ((SUPP f) SUBSET a))) `;;

(* ------------------------------------------------------------------ *)
(* compositions *)
(* ------------------------------------------------------------------ *)

let compose = new_definition
  `compose f g = \x. (f (g x))`;;

let COMP_ASSOC = prove_by_refinement(
   `!(f:num ->num) (g:num->num) (h:num->num).
      (compose f (compose g h)) = (compose (compose f g) h)`,
(* {{{ proof *)

   [
   REPEAT GEN_TAC THEN REWRITE_TAC[compose];
   ]);;
(* }}} *)

let COMP_INJ = prove (`!(f:A->B) (g:B->C) s t u.
      INJ f s t /\ (INJ g t u) ==>
  (INJ (compose g f) s u)`,
(* {{{ proof *)

   EVERY[REPEAT GEN_TAC;
   REWRITE_TAC[INJ;compose];
   DISCH_ALL_TAC;
   ASM_MESON_TAC[]]);;
(* }}} *)

let COMP_SURJ = prove (`!(f:A->B) (g:B->C) s t u.
   SURJ f s t /\ (SURJ g t u) ==> (SURJ (compose g f) s u)`,
(* {{{ proof *)

   EVERY[REWRITE_TAC[SURJ;compose];
   DISCH_ALL_TAC;
   ASM_MESON_TAC[]]);;
(* }}} *)

let COMP_BIJ = prove (`!(f:A->B) s t (g:B->C) u.
    BIJ f s t /\ (BIJ g t u) ==> (BIJ (compose g f) s u)`,
(* {{{ proof *)

   EVERY[
   REPEAT GEN_TAC;
   REWRITE_TAC[BIJ];
   DISCH_ALL_TAC;
   ASM_MESON_TAC[COMP_INJ;COMP_SURJ]]);;

(* }}} *)


(* ------------------------------------------------------------------ *)
(* general construction of an inverse function on a domain *)
(* ------------------------------------------------------------------ *)

let INVERSE_FN = prove_by_refinement(
  `?INV. (! (f:A->B) a b. (SURJ f a b) ==> ((INJ (INV f a b) b a) /\
       (!(x:B). (x IN b) ==> (f ((INV f a b) x) = x))))`,
(* {{{ proof *)

  [
  REWRITE_TAC[GSYM SKOLEM_THM];
  REPEAT GEN_TAC;
  MATCH_MP_TAC (prove_by_refinement( `!A B. (A ==> (?x. (B x))) ==> (?(x:B->A). (A ==> (B x)))`,[MESON_TAC[]])) ;
  REWRITE_TAC[SURJ;INJ];
  DISCH_ALL_TAC;
  SUBGOAL_TAC `?u. !y. ((y IN b)==> ((u y IN a) /\ ((f:A->B) (u y) = y)))`;
  REWRITE_TAC[GSYM SKOLEM_THM];
  GEN_TAC;
  ASM_MESON_TAC[];
  DISCH_THEN CHOOSE_TAC;
  EXISTS_TAC `u:B->A`;
  REPEAT CONJ_TAC;
  ASM_MESON_TAC[];
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (AP_TERM `f:A->B` th));
  ASM_MESON_TAC[];
  ASM_MESON_TAC[]
  ]);;

(* }}} *)

let INVERSE_DEF = new_specification ["INV"] INVERSE_FN;;

let INVERSE_BIJ = prove_by_refinement(
  `!(f:A->B) a b. (BIJ f a b) ==> ((BIJ (INV f a b) b a))`,
(* {{{ proof *)
  [
  REPEAT GEN_TAC;
  REWRITE_TAC[BIJ];
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[INVERSE_DEF];
  REWRITE_TAC[SURJ];
  CONJ_TAC;
  ASM_MESON_TAC[INVERSE_DEF;INJ];
  GEN_TAC THEN DISCH_TAC;
  EXISTS_TAC `(f:A->B) x`;
  CONJ_TAC;
  ASM_MESON_TAC[INJ];
  SUBGOAL_THEN `((f:A->B) x) IN b` ASSUME_TAC;
  ASM_MESON_TAC[INJ];
  SUBGOAL_THEN `(f:A->B) (INV f a b (f x)) = (f x)` ASSUME_TAC;
  ASM_MESON_TAC[INVERSE_DEF];
  H_UNDISCH_TAC (HYP "0");
  REWRITE_TAC[INJ];
  DISCH_ALL_TAC;
  FIRST_X_ASSUM (fun th -> MP_TAC (SPECL [`INV (f:A->B) a b (f x)`;`x:A`] th));
  ASM_REWRITE_TAC[];
  DISCH_ALL_TAC;
  SUBGOAL_THEN `INV (f:A->B) a b (f x) IN a` ASSUME_TAC;
  ASM_MESON_TAC[INVERSE_DEF;INJ];
  ASM_MESON_TAC[];
  ]);;
(* }}} *)

let INVERSE_XY = prove_by_refinement(
  `!(f:A->B) a b x y. (BIJ f a b) /\ (x IN a) /\ (y IN b) ==> ((INV f a b y = x) <=> (f x = y))`,
(* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  EQ_TAC;
  FIRST_X_ASSUM (fun th -> (ASSUME_TAC th THEN (ASSUME_TAC (MATCH_MP INVERSE_DEF (CONJUNCT2 (REWRITE_RULE[BIJ] th))))));
  ASM_MESON_TAC[];
  POP_ASSUM (fun th -> (ASSUME_TAC th THEN (ASSUME_TAC (CONJUNCT2 (REWRITE_RULE[INJ] (CONJUNCT1 (REWRITE_RULE[BIJ] th)))))));
  DISCH_THEN (fun th -> ASSUME_TAC th THEN (REWRITE_TAC[GSYM th]));
  FIRST_X_ASSUM  MATCH_MP_TAC;
  REPEAT CONJ_TAC;
  ASM_REWRITE_TAC[];
  IMP_RES_THEN ASSUME_TAC INVERSE_BIJ;
  ASM_MESON_TAC[BIJ;INJ];
  ASM_REWRITE_TAC[];
  FIRST_X_ASSUM (fun th -> (ASSUME_TAC (CONJUNCT2 (REWRITE_RULE[BIJ] th))));
  IMP_RES_THEN (fun th -> ASSUME_TAC (CONJUNCT2 th)) INVERSE_DEF;
  ASM_MESON_TAC[];
  ]);;
(* }}} *)

let FINITE_BIJ = prove(
  `!a b (f:A->B). FINITE a /\ (BIJ f a b) ==> (FINITE b)`,
(* {{{ proof *)

  MESON_TAC[SURJ_IMAGE;BIJ;INJ;FINITE_IMAGE]
);;

(* }}} *)

let FINITE_INJ = prove_by_refinement(
  `!a b (f:A->B). FINITE b /\ (INJ f a b) ==> (FINITE a)`,
(* {{{ proof *)

  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  MP_TAC (SPECL [`f:A->B`;`b:B->bool`;`a:A->bool`] FINITE_IMAGE_INJ_GENERAL);
  DISCH_ALL_TAC;
  SUBGOAL_THEN `(a:A->bool) SUBSET ({x | (x IN a) /\ ((f:A->B) x IN b)})` ASSUME_TAC;
  REWRITE_TAC[SUBSET];
  GEN_TAC ;
  REWRITE_TAC[IN_ELIM_THM];
  POPL_TAC[0;1];
  ASM_MESON_TAC[BIJ;INJ];
  MATCH_MP_TAC FINITE_SUBSET;
  EXISTS_TAC `({x | (x IN a) /\ ((f:A->B) x IN b)})` ;
  CONJ_TAC;
  FIRST_X_ASSUM (fun th -> MATCH_MP_TAC th);
  CONJ_TAC;
  ASM_MESON_TAC[BIJ;INJ];
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  ]
);;

(* }}} *)

let FINITE_BIJ2 = prove_by_refinement(
  `!a b (f:A->B). FINITE b /\ (BIJ f a b) ==> (FINITE a)`,
(* {{{ proof *)

  [
  MESON_TAC[BIJ;FINITE_INJ]
  ]);;
(* }}} *)

let BIJ_CARD = prove_by_refinement(
  `!a b (f:A->B). FINITE a /\ (BIJ f a b) ==> (CARD a = (CARD b))`,
(* {{{ proof *)

  [
  ASM_MESON_TAC[SURJ_IMAGE;BIJ;INJ;CARD_IMAGE_INJ];
  ]);;

(* }}} *)

let PAIR_LEMMA = prove_by_refinement(
   `!(x:num#num) i j. ((FST x = i) /\ (SND x = j)) <=> (x = (i,j))` ,
(* {{{ proof *)

   [
   MESON_TAC[FST;SND;PAIR];
   ]);;
(* }}} *)

let CARD_SING = prove_by_refinement(
      `!(u:A->bool). (SING u ) ==> (CARD u = 1)`,
(* {{{ proof *)
   [
   REWRITE_TAC[SING];
   GEN_TAC;
   DISCH_THEN (CHOOSE_TAC);
   ASM_REWRITE_TAC[];
   ASSUME_TAC FINITE_RULES;
   ASM_SIMP_TAC[CARD_CLAUSES;NOT_IN_EMPTY];
   ACCEPT_TAC (NUM_RED_CONV `SUC 0`)
   ]);;
(* }}} *)

let FINITE_SING = prove_by_refinement(
    `!(x:A). FINITE ({x})`,
(* {{{ proof *)

    [
    MESON_TAC[FINITE_RULES]
    ]);;
(* }}} *)

let NUM_INTRO = prove_by_refinement(
  `!f P.((!(n:num). !(g:A). (f g = n) ==> (P g)) ==> (!g. (P g)))`,
(* {{{ proof *)

  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  H_VAL (SPECL [`(f:A->num) (g:A)`; `g:A`]) (HYP "0");
  ASM_MESON_TAC[];
  ]);;
(* }}} *)



(* ------------------------------------------------------------------ *)
(* Lemmas about the support of a function *)
(* ------------------------------------------------------------------ *)


(* Law of cardinal exponents B^0 = 1 *)
let DOMAIN_EMPTY = prove_by_refinement(
  `!b. FUN (EMPTY:A->bool) b = { (\ (u:A). (CHOICE (UNIV:B->bool))) }`,
(* {{{ proof *)
  [
  GEN_TAC;
  REWRITE_TAC[EXTENSION;FUN];
  X_GEN_TAC `f:A->B`;
  REWRITE_TAC[IN_ELIM_THM;INSERT;NOT_IN_EMPTY;SUBSET_EMPTY;SUPP];
  REWRITE_TAC[EMPTY];
  ONCE_REWRITE_TAC[EXTENSION];
  REWRITE_TAC[IN];
  EQ_TAC;
  DISCH_TAC THEN (MATCH_MP_TAC EQ_EXT);
  BETA_TAC;
  ASM_REWRITE_TAC[];
  DISCH_TAC THEN (ASM_REWRITE_TAC[]) THEN BETA_TAC;
  ]);;
(* }}} *)

(* Law of cardinal exponents B^A * B = B^(A+1) *)
let DOMAIN_INSERT = prove_by_refinement(
  `!a b s. (~((s:A) IN a) ==>
      (?F.   (BIJ F (FUN (s INSERT a) b)
           { (u,v) | (u IN (FUN a b)) /\ ((v:B) IN b) }
           )))`,
(* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_TAC;
  EXISTS_TAC  `\ f. ((\ x. (if (x=(s:A)) then (CHOICE (UNIV:B->bool)) else (f x))),(f s))`;
  REWRITE_TAC[BIJ;INJ;SURJ];
  TAUT_TAC `(A /\ (A ==> B) /\ (A ==>C))  ==> ((A/\ B) /\ (A /\ C))`;
  REPEAT CONJ_TAC;
  X_GEN_TAC `(f:A->B)`;
  REWRITE_TAC[FUN;IN_ELIM_THM];
  REWRITE_TAC[INSERT;SUBSET];
  REWRITE_TAC[IN_ELIM_THM;SUPP];
  STRIP_TAC;
  ABBREV_TAC `g = \ x. (if (x=(s:A)) then (CHOICE (UNIV:B->bool)) else (f x)) `;
  EXISTS_TAC `g:A->B`;
  EXISTS_TAC `(f:A->B) s`;
  REWRITE_TAC[];
  REPEAT CONJ_TAC;
  EXPAND_TAC "g" THEN BETA_TAC;
  GEN_TAC;
  REWRITE_TAC[IN;COND_ELIM_THM];
  ASM_MESON_TAC[IN];
  (* next *) ALL_TAC;
  EXPAND_TAC "g" THEN BETA_TAC;
  GEN_TAC;
  ASM_CASES_TAC `(x:A) = s`;
  ASM_REWRITE_TAC[];
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* next *) ALL_TAC;
  ASM_MESON_TAC[];
  (* INJ *)  ALL_TAC;
  REWRITE_TAC[FUN;SUPP];
  DISCH_TAC;
  X_GEN_TAC `f1:A->B`;
  X_GEN_TAC `f2:A->B`;
  REWRITE_TAC[IN];
  DISCH_ALL_TAC;
  MATCH_MP_TAC EQ_EXT;
  GEN_TAC;
  ASM_CASES_TAC `(x:A) = s`;
  POPL_TAC[1;2;3;4;6;7];
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[PAIR;FST;SND];
  POPL_TAC[1;2;3;4;6;7];
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE[FST] (AP_TERM `FST:((A->B)#B)->(A->B)` th))) ;
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE[COND_ELIM_THM] (BETA_RULE (AP_THM th `x:A`))));
  LABEL_ALL_TAC;
  H_UNDISCH_TAC (HYP "0");
  COND_CASES_TAC;
  ASM_MESON_TAC[];
  ASM_MESON_TAC[];
  (* SURJ *) ALL_TAC;
  REWRITE_TAC[FUN;SUPP;IN_ELIM_THM];
  REWRITE_TAC[IN;INSERT;SUBSET];
  DISCH_ALL_TAC;
  X_GEN_TAC `p:(A->B)#B`;
  DISCH_THEN CHOOSE_TAC;
  FIRST_X_ASSUM (fun th -> MP_TAC th);
  DISCH_THEN CHOOSE_TAC;
  FIRST_X_ASSUM MP_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  EXISTS_TAC `\ (x:A). if (x = s) then (v:B) else (u x)`;
  REPEAT CONJ_TAC;
  X_GEN_TAC `t:A`;
  BETA_TAC;
  REWRITE_TAC[IN_ELIM_THM;COND_ELIM_THM];
  POPL_TAC[1;3;4;5];
  ASM_MESON_TAC[];
  X_GEN_TAC `t:A`;
  BETA_TAC;
  REWRITE_TAC[IN_ELIM_THM;COND_ELIM_THM];
  ASM_CASES_TAC `(t:A) = s`;
  POPL_TAC[1;3;4;5;6];
  ASM_REWRITE_TAC[];
  POPL_TAC[1;3;4;5;6];
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC `t:A` th));
  ASM_SIMP_TAC[prove(`~((t:A)=s) ==> ((t=s)=F)`,MESON_TAC[])];
  BETA_TAC;
  REWRITE_TAC[];
  POPL_TAC[0;2;3;4];
  AP_THM_TAC;
  AP_TERM_TAC;
  MATCH_MP_TAC EQ_EXT;
  X_GEN_TAC `t:A`;
  BETA_TAC;
  DISJ_CASES_TAC (prove(`(((t:A)=s) <=> T) \/ ((t=s) <=> F)`,MESON_TAC[]));
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[IN];
  ASM_REWRITE_TAC[]
  ]);;
(* }}} *)

let CARD_DELETE_CHOICE = prove_by_refinement(
  `!(a:(A->bool)). ((FINITE a) /\ (~(a=EMPTY))) ==>
   (SUC (CARD (a DELETE (CHOICE a))) = (CARD a))`,
(* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  ASM_SIMP_TAC[CARD_DELETE];
  ASM_SIMP_TAC[CHOICE_DEF];
  MATCH_MP_TAC (ARITH_RULE `~(x=0) ==> (SUC (x -| 1) = x)`);
  ASM_MESON_TAC[HAS_SIZE_0;HAS_SIZE];
  ]);;
(* }}} *)


(*
let dets_flag = ref true;;
dets_flag:= !labels_flag;;
*)


labels_flag:=false;;

(* Law of cardinals |B^A| = |B|^|A| *)
let FUN_SIZE = prove_by_refinement(
  `!b a. (FINITE (a:A->bool)) /\ (FINITE (b:B->bool))
          ==> ((FUN a b) HAS_SIZE ((CARD b) EXP (CARD a)))`,
(* {{{ proof *)
  [
  GEN_TAC;
  MATCH_MP_TAC (SPEC `CARD:(A->bool)->num` ((INST_TYPE) [`:A->bool`,`:A`]  NUM_INTRO));
  INDUCT_TAC;
  GEN_TAC;
  DISCH_ALL_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC [EXP];
  SUBGOAL_THEN `(a:A->bool) = EMPTY` ASSUME_TAC;
  ASM_REWRITE_TAC[GSYM HAS_SIZE_0;HAS_SIZE];
  ASM_REWRITE_TAC[HAS_SIZE;DOMAIN_EMPTY];
  CONJ_TAC;
  REWRITE_TAC[FINITE_SING];
  MATCH_MP_TAC CARD_SING;
  REWRITE_TAC[SING];
  MESON_TAC[];
  GEN_TAC;
  FIRST_X_ASSUM (fun th -> ASSUME_TAC (SPEC `(a:A->bool) DELETE (CHOICE a)` th)) ;
  DISCH_ALL_TAC;
  SUBGOAL_THEN `CARD ((a:A->bool) DELETE (CHOICE a)) = n` ASSUME_TAC;
  ASM_SIMP_TAC[CARD_DELETE];
  SUBGOAL_THEN `CHOICE (a:A->bool) IN a` ASSUME_TAC;
  MATCH_MP_TAC CHOICE_DEF;
  ASSUME_TAC( ARITH_RULE `!x. (x = (SUC n)) ==> (~(x = 0))`);
  REWRITE_TAC[GSYM HAS_SIZE_0;HAS_SIZE];
  ASM_MESON_TAC[];
  ASM_REWRITE_TAC[];
  MESON_TAC[ ( ARITH_RULE `!n. (SUC n -| 1) = n`)];
  LABEL_ALL_TAC;
  H_MATCH_MP (HYP "3") (HYP "4");
  SUBGOAL_THEN `FUN ((a:A->bool) DELETE CHOICE a) (b:B->bool) HAS_SIZE CARD b **| CARD (a DELETE CHOICE a)` ASSUME_TAC;
  ASM_MESON_TAC[FINITE_DELETE];
  ASSUME_TAC (SPECL [`((a:A->bool) DELETE (CHOICE a))`;`b:B->bool`;`(CHOICE (a:A->bool))` ] DOMAIN_INSERT);
  LABEL_ALL_TAC;
  H_UNDISCH_TAC (HYP "5");
  REWRITE_TAC[IN_DELETE];
  SUBGOAL_THEN `~((a:A->bool) = EMPTY)` ASSUME_TAC;
  REWRITE_TAC[GSYM HAS_SIZE_0;HAS_SIZE];
  ASSUME_TAC( ARITH_RULE `!x. (x = (SUC n)) ==> (~(x = 0))`);
  ASM_MESON_TAC[];
  ASM_SIMP_TAC[INSERT_DELETE;CHOICE_DEF];
  DISCH_THEN CHOOSE_TAC;
  REWRITE_TAC[HAS_SIZE];
  SUBGOAL_THEN `FINITE (FUN (a:A->bool) (b:B->bool))` ASSUME_TAC;
  (* CONJ_TAC; *) ALL_TAC;
  MATCH_MP_TAC (SPEC `FUN (a:A->bool) (b:B->bool)` (PINST[(`:A->B`,`:A`);(`:(A->B)#B`,`:B`)] [] FINITE_BIJ2));
  EXISTS_TAC `{u,v | (u:A->B) IN FUN (a DELETE CHOICE a) b /\ (v:B) IN b}`;
  EXISTS_TAC `F':(A->B)->((A->B)#B)`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC FINITE_PRODUCT;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[HAS_SIZE];
  ASM_REWRITE_TAC[];
  SUBGOAL_THEN `CARD (FUN (a:A->bool) (b:B->bool)) = (CARD {u,v | (u:A->B) IN FUN (a DELETE CHOICE a) b /\ (v:B) IN b})` ASSUME_TAC;
  MATCH_MP_TAC BIJ_CARD;
  EXISTS_TAC `F':(A->B)->((A->B)#B)`;
  ASM_REWRITE_TAC[];
  (* *) ALL_TAC;
  ASM_REWRITE_TAC[];
  SUBGOAL_THEN `FINITE (a DELETE CHOICE (a:A->bool))` ASSUME_TAC;
  ASM_MESON_TAC[FINITE_DELETE];
  SUBGOAL_THEN `(FUN ((a:A->bool) DELETE CHOICE a) (b:B->bool)) HAS_SIZE (CARD b **| (CARD (a DELETE CHOICE a)))` ASSUME_TAC;
  POPL_TAC[1;2;3;4;5;10;11];
  ASM_MESON_TAC[CARD_DELETE];
  POP_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE[HAS_SIZE] th) THEN (ASSUME_TAC th));
  ASM_SIMP_TAC[CARD_PRODUCT];
  REWRITE_TAC[EXP;MULT_AC]
  ]);;
(* }}} *)

labels_flag:= true;;


(* ------------------------------------------------------------------ *)
(* ------------------------------------------------------------------ *)



(* Definitions in math tend to be n-tuples of data.  Let's make it
   easy to pick out the individual components of a definition *)

(* pick out the rest of n-tuples. Indexing consistent with lib.drop *)
let drop0 = new_definition(`drop0 (u:A#B) = SND u`);;
let drop1 = new_definition(`drop1 (u:A#B#C) = SND (SND u)`);;
let drop2 = new_definition(`drop2 (u:A#B#C#D) = SND (SND (SND u))`);;
let drop3 = new_definition(`drop3 (u:A#B#C#D#E) = SND (SND (SND (SND u)))`);;

(* pick out parts of n-tuples *)

let part0 = new_definition(`part0 (u:A#B) = FST u`);;
let part1 = new_definition(`part1 (u:A#B#C) = FST (drop0 u)`);;
let part2 = new_definition(`part2 (u:A#B#C#D) = FST (drop1 u)`);;
let part3 = new_definition(`part3 (u:A#B#C#D#E) = FST (drop2 u)`);;
let part4 = new_definition(`part4 (u:A#B#C#D#E#F) = FST (drop3 u)`);;
let part5 = new_definition(`part5 (u:A#B#C#D#E#F#G) =
   FST (SND (SND (SND (SND (SND u)))))`);;
let part6 = new_definition(`part6 (u:A#B#C#D#E#F#G#H) =
   FST (SND (SND (SND (SND (SND (SND u))))))`);;
let part7 = new_definition(`part7 (u:A#B#C#D#E#F#G#H#I) =
   FST (SND (SND (SND (SND (SND (SND (SND u)))))))`);;


(* ------------------------------------------------------------------ *)
(* Basic Definitions of Euclidean Space, Metric Spaces, and Topology *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Interface *)
(* ------------------------------------------------------------------ *)

let euclid_def = local_definition "euclid";;
mk_local_interface "euclid";;

overload_interface
 ("+", `euclid'euclid_plus:(num->real)->(num->real)->(num->real)`);;

make_overloadable "*#" `:A -> B -> B`;;

let euclid_scale = euclid_def
  `euclid_scale t f = \ (i:num). (t*. (f i))`;;

overload_interface ("*#",`euclid'euclid_scale`);;

parse_as_infix("*#",(20,"right"));;

let euclid_neg = euclid_def `euclid_neg f = \ (i:num). (--. (f i))`;;

(* This is highly ambiguous: -- f x can be read as
   (-- f) x or as -- (f x).  *)
overload_interface ("--",`euclid'euclid_neg`);;

overload_interface
  ("-", `euclid'euclid_minus:(num->real)->(num->real)->(num->real)`);;

(* ------------------------------------------------------------------ *)
(* Euclidean Space *)
(* ------------------------------------------------------------------ *)

let euclid_plus = euclid_def
  `euclid_plus f g = \ (i:num). (f i) +. (g i)`;;

let euclid = euclid_def `euclid n v <=> !m. (n <=| m) ==> (v m = &.0)`;;

let euclidean = euclid_def `euclidean v <=> ?n. euclid n v`;;

let euclid_minus = euclid_def
  `euclid_minus f g = \(i:num). (f i) -. (g i)`;;

let euclid0 = euclid_def `euclid0 = \(i:num). &.0`;;

let coord = euclid_def `coord i (f:num->real) = f i`;;

let dot = euclid_def `dot f g =
  let (n = (min_num (\m. (euclid m f) /\ (euclid m g)))) in
  sum (0,n) (\i. (f i)*(g i))`;;

let norm = euclid_def `norm f = sqrt(dot f f)`;;

let d_euclid = euclid_def `d_euclid f g = norm (f - g)`;;



(* ------------------------------------------------------------------ *)
(* Euclidean and Convex geometry *)
(* ------------------------------------------------------------------ *)


let sum_vector_EXISTS = prove_by_refinement(
  `?sum_vector. (!f n. sum_vector(n,0) f = (\n. &.0)) /\
    (!f m n. sum_vector(n,SUC m) f = sum_vector(n,m) f + f(n + m))`,
  (* {{{ proof *)
  [
  (CHOOSE_TAC o prove_recursive_functions_exist num_RECURSION) `(!f n. sm n 0 f = (\n. &0)) /\ (!f m n. sm  n (SUC m) f = sm n m f + f(n + m))`;
  EXISTS_TAC `\(n,m) f. (sm:num->num->(num->(num->real))->(num->real)) n m f`;
  CONV_TAC(DEPTH_CONV GEN_BETA_CONV);
  ASM_REWRITE_TAC[];
  ]);;
  (* }}} *)

let sum_vector = new_specification ["sum_vector"] sum_vector_EXISTS;;

let mk_segment = euclid_def
  `mk_segment x y = { u | ?a. (&.0 <=. a) /\ (a <=. &.1) /\
        (u = a *# x + (&.1 - a) *# y) }`;;

let mk_open_segment = euclid_def
  `mk_open_segment x y = { u | ?a. (&.0 <. a) /\ (a <. &.1) /\
        (u = a *# x + (&.1 - a) *# y) }`;;

let convex = euclid_def
  `convex S <=> !x y. (S x) /\ (S y) ==> (mk_segment x y SUBSET S)`;;

let convex_hull = euclid_def
  `convex_hull S = { u | ?f alpha m. (!n. (n< m) ==> (S (f n))) /\
    (sum(0,m) alpha = &.1) /\ (!n. (n< m) ==> (&.0 <=. (alpha n))) /\
    (u = sum_vector(0,m) (\n. (alpha n) *# (f n)))}`;;

let affine_hull = euclid_def
  `affine_hull S = { u | ?f alpha m. (!n. (n< m) ==> (S (f n))) /\
    (sum(0,m) alpha = &.1) /\
    (u = sum_vector(0,m) (\n. (alpha n) *# (f n)))}`;;

let mk_line = euclid_def `mk_line x y =
   {z| ?t. (z = (t *# x) + ((&.1 - t) *# y)) }`;;

let affine = euclid_def
  `affine S <=> !x y. (S x ) /\ (S y) ==> (mk_line x y SUBSET S)`;;

let affine_dim = euclid_def
  `affine_dim n S <=>
    (?T. (T HAS_SIZE (SUC n)) /\ (affine_hull T = affine_hull S)) /\
    (!T m. (T HAS_SIZE (SUC m)) /\ (m < n) ==> ~(affine_hull T = affine_hull S))`;;

let collinear = euclid_def
  `collinear S <=> (?n. affine_dim n S /\ (n < 2))`;;

let coplanar = euclid_def
  `coplanar S <=> (?n. affine_dim n S /\ (n < 3))`;;

let line = euclid_def
  `line L <=> (affine L) /\ (affine_dim 1 L)`;;

let plane = euclid_def
  `plane P <=> (affine P) /\ (affine_dim 2 P)`;;

let space = euclid_def
  `space R <=> (affine R) /\ (affine_dim 3 R)`;;

(*

General constructor of conical objects, including
  rays, cones, half-planes, etc.

L is the edge.  C is the set of generators in the positive
direction.

If L is a line, and C = {c}, we get the half-plane bounded by
L and containing c.

If L is a point, and C is general, we get the cone at L generated
by C.

If L and C are both singletons, we get the ray ending at L.

  *)

let mk_open_half_set = euclid_def
  `mk_open_half_set L S  =
   { u | ?t v c. (L v) /\ (S c) /\ (&.0 < t) /\
      (u = (t *# (c - v) + (&.1 - t) *# v)) }`;;

let mk_half_set = euclid_def
  `mk_half_set L S  =
   { u | ?t v c. (L v) /\ (S c) /\ (&.0 <=. t) /\
      (u = (t *# (c - v) + (&.1 - t) *# v)) }`;;


let mk_angle = euclid_def `mk_angle x y z =
   (mk_half_set {x} {y}) UNION (mk_half_set {x} {z})`;;

let mk_signed_angle = euclid_def `mk_signed_angle x y z =
   (mk_half_set {x} {y} , mk_half_set {x} {z})`;;

let mk_convex_cone = euclid_def
  `mk_convex_cone v (S:(num->real)->bool) =
    mk_half_set {v} (convex_hull S)`;;

(* we always normalize the radius of balls in a packing to 1 *)
let packing = euclid_def(`packing (S:(num->real)->bool) <=>
        !x y. ( ((S x) /\ (S y) /\ ((d_euclid x y) < (&.2))) ==>
                (x = y))`);;

let saturated_packing = euclid_def(`saturated_packing S <=>
        (( packing S) /\
        (!z. (affine_hull S z)  ==>
               (?x. ((S x) /\ ((d_euclid x z) < (&.2))))))`);;


(* 3 dimensions specific:  *)
let cross_product3 = euclid_def(`cross_product3 v1 v2 =
        let (x1 = v1 0) and (x2 = v1 1) and (x3 = v1 2) in
        let (y1 = v2 0) and (y2 = v2 1) and (y3 = v2 2) in
        (\k.
                (if (k=0) then (x2*y3-x3*y2)
                else if (k=1) then (x3*y1-x1*y3)
                else if (k=2) then (x1*y2-x2*y1)
                else (&0)))`);;

let triple_product = euclid_def(`triple_product v1 v2 v3 =
        dot v1 (cross_product3 v2 v3)`);;

(* the bounding edge *)
let mk_triangle = euclid_def `mk_triangle v1 v2 v3 =
  (mk_segment v1 v2) UNION (mk_segment v2 v3) UNION (mk_segment v3 v1)`;;

(* the interior *)
let mk_interior_triangle = euclid_def
  `mk_interior_triangle v1 v2 v3 =
     mk_open_half_set (mk_line v1 v2) {v3} INTER
       (mk_open_half_set (mk_line v2 v3) {v1}) INTER
       (mk_open_half_set (mk_line v3 v1) {v2})`;;

let mk_triangular_region = euclid_def
  `mk_triangular_region v1 v2 v3 =
    (mk_triangle v1 v2 v3) UNION (mk_interior_triangle v1 v2 v3)`;;


(* ------------------------------------------------------------------ *)
(* Statements of Theorems in Euclidean Geometry (no proofs *)
(* ------------------------------------------------------------------ *)

let half_set_convex = `!L S. convex (mk_half_set L S)`;;

let open_half_set_convex = `!L S . convex (mk_open_half_set L S )`;;

let affine_dim0 = `!S. (affine_dim 0 S) = (SING S)`;;

let hull_convex = `!S. (convex (convex_hull S))`;;

let hull_minimal = `!S T. (convex T) /\ (S SUBSET T) ==>
     (convex_hull S) SUBSET T`;;

let affine_hull_affine = `!S. (affine (affine_hull S))`;;

let affine_hull_minimal = `!S T. (affine T) /\ (S SUBSET T) ==>
     (affine_hull S) SUBSET T`;;

let mk_line_dim = `!x y. ~(x = y) ==> affine_dim 1 (mk_line x y)`;;

let affine_convex_hull = `!S. (affine_hull S) = (affine_hull (convex_hull S))`;;

let convex_hull_hull = `!S. (convex_hull S) = (convex_hull (convex_hull S))`;;

let euclid_affine_dim = `!n. affine_dim n (euclid n)`;;

let affine_dim_subset = `!m n T S.
  (affine_dim m T) /\ (affine_dim n S) /\ (T SUBSET S) ==> (m <= n)`;;

(* A few of the Birkhoff postulates of Geometry (incomplete) *)

let line_postulate = `!x y. ~(x = y) ==>
   (?!L. (L x) /\ (L y) /\ (line L))`;;

let ruler_postulate = `!L. (line L) ==>
  (?f. (BIJ f L UNIV) /\
  (!x y. (L x /\ L y ==> (d_euclid x y = abs(f x -. f y)))))`;;

let affine_postulate = `!n. (affine_dim n P) ==> (?S.
  (S SUBSET P) /\ (S HAS_SIZE n) /\ (affine_dim n S))`;;

let line_plane = `!P x y. (plane P) /\ (P x) /\ (P y) ==>
  (mk_line x y SUBSET P)`;;

let plane_of_pt = `!S. (S HAS_SIZE 3) ==> (?P. (plane P) /\
   (S SUBSET P))`;;

let plane_of_pt_unique = `!S. (S HAS_SIZE 3) ==> (collinear S) \/
  (?! P. (plane P) /\ (S SUBSET P))`;;

let plane_inter = `!P Q. (plane P) /\ (plane Q) ==>
  (P INTER Q = EMPTY) \/ (line (P INTER Q)) \/ (P = Q)`;;

(* each line separates a plane into two half-planes *)
let plane_separation =
  `!P L. (plane P) /\ (line L) /\ (L SUBSET P) ==>
  (?A B. (A INTER B = EMPTY) /\ (A INTER L = EMPTY) /\
    (B INTER L = EMPTY) /\ (L UNION A UNION B = P) /\
   (!c u. (P c) /\ (u = mk_open_half_set L {c}) ==>
      (u = A) \/ (u = B) \/ (u = L)) /\
   (!a b. (A a) /\ (B b) ==> ~(segment a b INTER L = EMPTY)))`;;

let space_separation =
  `!R P. (space R) /\ (plane P) /\ (P SUBSET R) ==>
  (?A B. (A INTER B = EMRTY) /\ (A INTER P = EMRTY) /\
    (B INTER P = EMRTY) /\ (P UNION A UNION B = R) /\
   (!c u. (R c) /\ (u = mk_open_half_set P {c}) ==>
      (u = A) \/ (u = B) \/ (u = P)) /\
     (!a b. (A a) /\ (B b) ==> ~(segment a b INTER L = EMPTY)))`;;

(* ------------------------------------------------------------------ *)
(* Metric Space *)
(* ------------------------------------------------------------------ *)

let metric_space = euclid_def `metric_space (X:A->bool,d:A->A->real)
   <=>
   !x y z.
      (X x) /\ (X y) /\ (X z) ==>
         (((&.0) <=. (d x y)) /\
          ((&.0 = d x y) = (x = y)) /\
          (d x y = d y x) /\
          (d x z <=. d x y + d y z))`;;

(* ------------------------------------------------------------------ *)
(* Measure *)
(* ------------------------------------------------------------------ *)

let set_translate = euclid_def
  `set_translate v X = { z | ?x. (X x) /\ (z = v + x) }`;;

let set_scale = euclid_def
  `set_scale r X = { z | ?x. (X x) /\ (z = r *# x) }`;;

let mk_rectangle = euclid_def
  `mk_rectangle a b = { z | !(i:num). (a i <=. z i) /\ (z i <. b i) }`;;

let one_vec = euclid_def
  `one_vec n = (\i. if (i<| n) then (&.1) else (&.0))`;;

let mk_cube = euclid_def
  `mk_cube n k v =
    let (r = twopow (--: (&: k))) in
    let (vv = (\i. (real_of_int (v i)))) in
     mk_rectangle (r *# vv) (r *# (vv + (one_vec n)))`;;

let inner_cube = euclid_def
  `inner_cube n k A =
    { v | (mk_cube n k v SUBSET A) /\
      (!i. (n <| i) ==> (&:0 = v i)) }`;;

let outer_cube = euclid_def
  `outer_cube n k A =
    { v | ~((mk_cube n k v) INTER A = EMPTY) /\
      (!i. (n <| i) ==> (&:0 = v i)) }`;;

let inner_vol = euclid_def
  `inner_vol n k A =
    (&. (CARD (inner_cube n k A)))*(twopow (--: (&: (n*k))))`;;

let outer_vol = euclid_def
  `outer_vol n k A =
    (&. (CARD (outer_cube n k A)))*(twopow (--: (&: (n*k))))`;;

let euclid_bounded = euclid_def
  `euclid_bounded A = (?R. !(x:num->real) i. (A x) ==> (x i <. R))`;;

let vol = euclid_def
  `vol n A = lim (\k. outer_vol n k A)`;;

(* ------------------------------------------------------------------ *)
(* COMPUTING PI *)
(* ------------------------------------------------------------------ *)

unambiguous_interface();;
prioritize_real();;

(* ------------------------------------------------------------------ *)
(* general series approximations *)
(* ------------------------------------------------------------------ *)

let SER_APPROX1 = prove_by_refinement(
  `!s f g.  (f sums s) /\ (summable g) ==>
    (!k. ((!n. (||. (f (n+k)) <=. (g (n+k)))) ==>
    ( (s - (sum(0,k) f)) <=. (suminf (\n. (g (n +| k)))))))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  DISCH_TAC;
  IMP_RES_THEN ASSUME_TAC SUM_SUMMABLE;
  IMP_RES_THEN (fun th -> (ASSUME_TAC (SPEC `k:num` th))) SER_OFFSET;
  IMP_RES_THEN ASSUME_TAC SUM_UNIQ;
  SUBGOAL_THEN `(\n. (f (n+ k))) sums (s - (sum(0,k) f))` ASSUME_TAC;
  ASM_MESON_TAC[];
  SUBGOAL_THEN `summable (\n. (f (n+k))) /\ (suminf (\n. (f (n+k))) <=. (suminf (\n. (g (n+k)))))` ASSUME_TAC;
  MATCH_MP_TAC SER_LE2;
  BETA_TAC;
  ASM_REWRITE_TAC[];
  IMP_RES_THEN ASSUME_TAC SER_OFFSET;
  FIRST_X_ASSUM (fun th -> ACCEPT_TAC (MATCH_MP SUM_SUMMABLE (((SPEC `k:num`) th))));
  ASM_MESON_TAC[SUM_UNIQ]
  ]);;
  (* }}} *)

let SER_APPROX = prove_by_refinement(
  `!s f g.  (f sums s) /\ (!n. (||. (f n) <=. (g n))) /\
       (summable g) ==>
    (!k. (abs (s - (sum(0,k) f)) <=. (suminf (\n. (g (n +| k))))))`,
  (* {{{ proof *)
  [
  REPEAT GEN_TAC;
  DISCH_ALL_TAC;
  GEN_TAC;
  REWRITE_TAC[REAL_ABS_BOUNDS];
  CONJ_TAC;
  SUBGOAL_THEN `(!k. ((!n. (||. ((\p. (--. (f p))) (n+k))) <=. (g (n+k)))) ==> ((--.s) - (sum(0,k) (\p. (--. (f p)))) <=. (suminf (\n. (g (n +k))))))` ASSUME_TAC;
  MATCH_MP_TAC SER_APPROX1;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC SER_NEG ;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC (REAL_ARITH (`(--. s -. (--. u) <=. x) ==> (--. x <=. (s -. u))`));
  ONCE_REWRITE_TAC[GSYM SUM_NEG];
  FIRST_X_ASSUM (fun th -> (MATCH_MP_TAC th));
  BETA_TAC;
  ASM_REWRITE_TAC[REAL_ABS_NEG];
  H_VAL2 CONJ (HYP "0") (HYP "2");
  IMP_RES_THEN MATCH_MP_TAC SER_APPROX1 ;
  GEN_TAC;
  ASM_MESON_TAC[];
  ]);;
  (* }}} *)

(* ------------------------------------------------------------------ *)
(* now for pi calculation stuff *)
(* ------------------------------------------------------------------ *)


let local_def = local_definition "trig";;


let PI_EST = prove_by_refinement(
               `!n. (1 <=| n) ==> (abs(&4 / &(8 * n + 1) -
            &2 / &(8 * n + 4) -
            &1 / &(8 * n + 5) -
            &1 / &(8 * n + 6)) <= &.622/(&.819))`,
  (* {{{ proof *)
   [
   GEN_TAC THEN DISCH_ALL_TAC;
   REWRITE_TAC[real_div];
   MATCH_MP_TAC (REWRITE_RULE[real_div] (REWRITE_RULE[REAL_RAT_REDUCE_CONV `(&.4/(&.9) +(&.2/(&.12)) + (&.1/(&.13))+ (&.1/(&.14)))`] (REAL_ARITH `(abs((&.4)*.u)<=. (&.4)/(&.9)) /\ (abs((&.2)*.v)<=. (&.2)/(&.12)) /\ (abs((&.1)*w) <=. (&.1)/(&.13)) /\ (abs((&.1)*x) <=. (&.1)/(&.14)) ==> (abs((&.4)*u -(&.2)*v - (&.1)*w - (&.1)*x) <= (&.4/(&.9) +(&.2/(&.12)) + (&.1/(&.13))+ (&.1/(&.14))))`)));
   IMP_RES_THEN ASSUME_TAC (ARITH_RULE `1 <=| n ==> (0 < n)`);
   FIRST_X_ASSUM (fun th -> ASSUME_TAC (REWRITE_RULE[GSYM REAL_OF_NUM_LT] th));
   ASSUME_TAC (prove(`(a<=.b) ==> (&.n*a <=. (&.n)*b)`,MESON_TAC[REAL_PROP_LE_LMUL;REAL_POS]));
   REWRITE_TAC[REAL_ABS_MUL;REAL_ABS_INV;prove(`||.(&.n) = (&.n)`,MESON_TAC[REAL_POS;REAL_ABS_REFL])];
   REPEAT CONJ_TAC THEN (POP_ASSUM (fun th -> MATCH_MP_TAC th)) THEN (MATCH_MP_TAC (prove(`((&.0 <. (&.n)) /\ (&.n <=. a)) ==> (inv(a)<=. (inv(&.n)))`,MESON_TAC[REAL_ABS_REFL;REAL_ABS_INV;REAL_LE_INV2]))) THEN
   REWRITE_TAC[REAL_LT;REAL_LE] THEN (H_UNDISCH_TAC (HYP"0")) THEN
   ARITH_TAC]);;
  (* }}} *)

let pi_fun = local_def `pi_fun n = inv (&.16 **. n) *.
          (&.4 / &.(8 *| n +| 1) -.
           &.2 / &.(8 *| n +| 4) -.
           &.1 / &.(8 *| n +| 5) -.
           &.1 / &.(8 *| n +| 6))`;;

let pi_bound_fun = local_def `pi_bound_fun n = if (n=0) then (&.8) else
    (((&.15)/(&.16))*(inv(&.16 **. n))) `;;

let PI_EST2 = prove_by_refinement(
    `!k. abs(pi_fun k) <=. (pi_bound_fun k)`,
  (* {{{ proof *)
   [
   GEN_TAC;
   REWRITE_TAC[pi_fun;pi_bound_fun];
   COND_CASES_TAC;
   ASM_REWRITE_TAC[];
   CONV_TAC (NUM_REDUCE_CONV);
   (CONV_TAC (REAL_RAT_REDUCE_CONV));
   CONV_TAC (RAND_CONV (REWR_CONV (REAL_ARITH `a*b = b*.a`)));
   REWRITE_TAC[REAL_ABS_MUL;REAL_ABS_INV;REAL_ABS_POW;prove(`||.(&.n) = (&.n)`,MESON_TAC[REAL_POS;REAL_ABS_REFL])];
   MATCH_MP_TAC (prove(`!x y z. (&.0 <. z /\ (y <=. x) ==> (z*y <=. (z*x)))`,MESON_TAC[REAL_LE_LMUL_EQ]));
   ASSUME_TAC (REWRITE_RULE[] (REAL_RAT_REDUCE_CONV `(&.622)/(&.819) <=. (&.15)/(&.16)`));
   IMP_RES_THEN ASSUME_TAC (ARITH_RULE `~(k=0) ==> (1<=| k)`);
   IMP_RES_THEN ASSUME_TAC (PI_EST);
   CONJ_TAC;
   SIMP_TAC[REAL_POW_LT;REAL_LT_INV;ARITH_RULE `&.0 < (&.16)`];
   ASM_MESON_TAC[REAL_LE_TRANS];
   ]);;
  (* }}} *)

let GP16 = prove_by_refinement(
  `!k. (\n. inv (&16 pow k) * inv (&16 pow n)) sums
         inv (&16 pow k) * &16 / &15`,
  (* {{{ proof *)
  [
  GEN_TAC;
  ASSUME_TAC (REWRITE_RULE[] (REAL_RAT_REDUCE_CONV `abs (&.1 / (&. 16)) <. (&.1)`));
  IMP_RES_THEN (fun th -> ASSUME_TAC (CONV_RULE REAL_RAT_REDUCE_CONV th)) GP;
  MATCH_MP_TAC SER_CMUL;
  ASM_REWRITE_TAC[GSYM REAL_POW_INV;REAL_INV_1OVER];
  ]);;
  (* }}} *)

let GP16a = prove_by_refinement(
   `!k. (0<|k) ==> (\n. (pi_bound_fun (n+k))) sums (inv(&.16 **. k))`,
  (* {{{ proof *)
   [
   GEN_TAC;
   DISCH_TAC;
   SUBGOAL_THEN `(\n. pi_bound_fun (n+k)) = (\n. ((&.15/(&.16))* (inv(&.16)**. k) *. inv(&.16 **. n)))` (fun th-> REWRITE_TAC[th]);
   MATCH_MP_TAC EQ_EXT;
   X_GEN_TAC `n:num` THEN BETA_TAC;
   REWRITE_TAC[pi_bound_fun];
   COND_CASES_TAC;
   ASM_MESON_TAC[ARITH_RULE `0<| k ==> (~(n+k = 0))`];
   REWRITE_TAC[GSYM REAL_MUL_ASSOC];
   AP_TERM_TAC;
   REWRITE_TAC[REAL_INV_MUL;REAL_POW_ADD;REAL_POW_INV;REAL_MUL_AC];
   SUBGOAL_THEN `(\n. (&.15/(&.16)) *. ((inv(&.16)**. k)*. inv(&.16 **. n))) sums ((&.15/(&.16)) *.(inv(&.16**. k)*. ((&.16)/(&.15))))` ASSUME_TAC;
   MATCH_MP_TAC SER_CMUL;
   REWRITE_TAC[REAL_POW_INV];
   ACCEPT_TAC (SPEC `k:num` GP16);
   FIRST_X_ASSUM MP_TAC;
   REWRITE_TAC[REAL_MUL_ASSOC];
   MATCH_MP_TAC (prove (`(x=y) ==> ((a sums x) ==> (a sums y))`,MESON_TAC[]));
   MATCH_MP_TAC (REAL_ARITH `(b*(a*c) = (b*(&.1))) ==> ((a*b)*c = b)`);
   AP_TERM_TAC;
   CONV_TAC (REAL_RAT_REDUCE_CONV);
   ]);;
  (* }}} *)

let PI_SER = prove_by_refinement(
  `!k. (0<|k) ==> (abs(pi - (sum(0,k) pi_fun)) <=. (inv(&.16 **. (k))))`,
  (* {{{ proof *)
   [
   GEN_TAC THEN DISCH_TAC;
   ASSUME_TAC (ONCE_REWRITE_RULE[ETA_AX] (REWRITE_RULE[GSYM pi_fun] POLYLOG_THM));
   ASSUME_TAC PI_EST2;
   IMP_RES_THEN (ASSUME_TAC) GP16a;
   IMP_RES_THEN (ASSUME_TAC) SUM_SUMMABLE;
   IMP_RES_THEN (ASSUME_TAC) SER_OFFSET_REV;
   IMP_RES_THEN (ASSUME_TAC) SUM_SUMMABLE;
   MP_TAC (SPECL [`pi`;`pi_fun`;`pi_bound_fun` ] SER_APPROX);
   ASM_REWRITE_TAC[];
   DISCH_THEN (fun th -> MP_TAC (SPEC `k:num` th));
   SUBGOAL_THEN `suminf (\n. pi_bound_fun (n + k)) = inv (&.16 **. k)` (fun th -> (MESON_TAC[th]));
   ASM_MESON_TAC[SUM_UNIQ];
   ]);;
  (* }}} *)

(* replace 3 by SUC (SUC (SUC 0)) *)
let SUC_EXPAND_CONV tm =
   let count = dest_numeral tm in
   let rec add_suc i r =
     if (i <=/ (num 0)) then r
     else add_suc (i -/ (num 1)) (mk_comb (`SUC`,r)) in
   let tm' = add_suc count `0` in
   REWRITE_RULE[] (ARITH_REWRITE_CONV[] (mk_eq (tm,tm')));;

let inv_twopow = prove(
  `!n. inv (&.16 **. n) = (twopow (--: (&:(4*n)))) `,
    REWRITE_TAC[TWOPOW_NEG;GSYM (NUM_RED_CONV `2 EXP 4`);
    REAL_OF_NUM_POW;EXP_MULT]);;

let PI_SERn n =
   let SUM_EXPAND_CONV =
           (ARITH_REWRITE_CONV[]) THENC
           (TOP_DEPTH_CONV SUC_EXPAND_CONV) THENC
           (REWRITE_CONV[sum]) THENC
           (ARITH_REWRITE_CONV[REAL_ADD_LID;GSYM REAL_ADD_ASSOC]) in
   let sum_thm = SUM_EXPAND_CONV (vsubst [n,`i:num`] `sum(0,i) f`) in
   let gt_thm = ARITH_RULE (vsubst [n,`i:num`] `0 <| i`) in
   ((* CONV_RULE REAL_RAT_REDUCE_CONV *)(CONV_RULE (ARITH_REWRITE_CONV[]) (BETA_RULE (REWRITE_RULE[sum_thm;pi_fun;inv_twopow] (MATCH_MP PI_SER gt_thm)))));;

(* abs(pi - u ) < e *)
let recompute_pi bprec =
   let n = (bprec /4) in
   let pi_ser = PI_SERn (mk_numeral (num n)) in
   let _ = remove_real_constant `pi` in
   (add_real_constant pi_ser; INTERVAL_OF_TERM bprec `pi`);;

(* ------------------------------------------------------------------ *)
(* restore defaults *)
(* ------------------------------------------------------------------ *)

reduce_local_interface("trig");;
pop_priority();;







