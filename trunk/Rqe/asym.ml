override_interface ("-->",`(tends_num_real)`);;
prioritize_real();;

(* ---------------------------------------------------------------------- *)
(*  properites of num sequences                                           *)
(* ---------------------------------------------------------------------- *)

let LIM_INV_1N = prove_by_refinement(
  `(\n. &1 / &n) --> &0`,
(* {{{ Proof *)

[
  REWRITE_TAC[SEQ;real_sub;REAL_ADD_RID;REAL_NEG_0;real_gt;real_ge;GT;GE];
  REPEAT STRIP_TAC;
  MP_TAC (ISPEC `&2 / e` REAL_ARCH_SIMPLE);
  STRIP_TAC;
  EXISTS_TAC `n`;
  REPEAT STRIP_TAC;
  CLAIM `&0 < &2 / e`;
  ASM_MESON_TAC[REAL_LT_RDIV_0;REAL_ARITH `&0 < &2`];
  STRIP_TAC;
  CLAIM `&0 < &n`;
  ASM_MESON_TAC[REAL_LTE_TRANS;REAL_LE];
  STRIP_TAC;
  CLAIM `&0 < &n'`;
  ASM_MESON_TAC[REAL_LTE_TRANS;REAL_LE];
  STRIP_TAC;
  CLAIM `~(&n' = &0)`;
  ASM_MESON_TAC[REAL_LT_IMP_NZ];
  STRIP_TAC;
  ASM_SIMP_TAC[ABS_DIV];
  REWRITE_TAC[REAL_ABS_NUM];
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ];
  CLAIM `&2 <= e * &n`;
  ASM_MESON_TAC[REAL_LE_LDIV_EQ;REAL_MUL_SYM];
  STRIP_TAC;
  CLAIM `e * &n <= e * &n'`;
  MATCH_MP_TAC REAL_LE_LMUL;
  ASM_MESON_TAC [REAL_LT_LE;REAL_LE];
  STRIP_TAC;
  ASM_MESON_TAC[REAL_LTE_TRANS;REAL_LE_TRANS;REAL_ARITH `&1 < &2`];
]);;

(* }}} *)

let LIM_INV_CONST = prove_by_refinement(
  `!c. (\n. c / &n) --> &0`,
(* {{{ Proof *)

[
  ONCE_REWRITE_TAC[REAL_ARITH  `c / &n = c * &1 / &n`];
  STRIP_TAC;
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[REAL_ARITH `&0 = c * &0`]));
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC THENL [MATCH_ACCEPT_TAC SEQ_CONST;MATCH_ACCEPT_TAC LIM_INV_1N];
]);;

(* }}} *)

let LIM_INV_1NP = prove_by_refinement(
  `!c k. 0 < k ==> (\n. c / &n pow k) --> &0`,
(* {{{ Proof *)
[
  STRIP_TAC;
  INDUCT_TAC;
  REWRITE_TAC[ARITH_RULE `~(0 < 0)`];
  REWRITE_TAC[real_pow;REAL_DIV_DISTRIB_R];
  STRIP_TAC;
  CASES_ON `k = 0`;
  ASM_REWRITE_TAC[real_pow;GSYM REAL_DIV_DISTRIB_R;REAL_MUL_RID];
  MATCH_ACCEPT_TAC LIM_INV_CONST;
  CLAIM `(\n. c / &n pow k) --> &0`;
  FIRST_ASSUM MATCH_MP_TAC;
  EVERY_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `&0 = &0 * &0`];
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC THENL [MATCH_ACCEPT_TAC LIM_INV_1N;FIRST_ASSUM MATCH_ACCEPT_TAC];
]);;
(* }}} *)

let LIM_INV_CON = prove_by_refinement(
  `!c d k. 0 < k ==> (\n. c / (d * &n pow k)) --> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[REAL_DIV_DISTRIB_R];
  REPEAT STRIP_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `&0 = (&1 / d) * &0`];
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC;
  MATCH_ACCEPT_TAC SEQ_CONST;
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC LIM_INV_1NP;
]);;
(* }}} *)

let LIM_NN = prove_by_refinement(
  `(\n. &n / &n) --> &1`,
(* {{{ Proof *)
[
  REWRITE_TAC[SEQ];
  REPEAT STRIP_TAC;
  EXISTS_TAC `1`;
  REWRITE_TAC[GT;GE];
  REPEAT STRIP_TAC;
  CLAIM `~(&n = &0)`;
  MATCH_MP_TAC REAL_LT_IMP_NZ;
  ASM_MESON_TAC[REAL_LE;REAL_ARITH `&0 < &1`;REAL_LTE_TRANS];
  STRIP_TAC;
  ASM_SIMP_TAC[REAL_DIV_REFL;real_sub;REAL_ADD_RINV;ABS_0];
]);;
(* }}} *)

let LIM_NNC = prove_by_refinement(
  `~(k = &0) ==> (\n. (k * &n) / (k * &n)) --> &1`,
(* {{{ Proof *)
[
  REWRITE_TAC[REAL_DIV_DISTRIB_2];
  ONCE_REWRITE_TAC[REAL_ARITH `&1 = &1 * &1`];
  STRIP_TAC;
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC;
  ASM_SIMP_TAC[real_div;REAL_MUL_RINV];
  MATCH_ACCEPT_TAC SEQ_CONST;
  MATCH_ACCEPT_TAC LIM_NN;
]);;
(* }}} *)

let LIM_MONO = prove_by_refinement(
  `!c d a b. ~(d = &0) /\ a < b ==> (\n. (c * &n pow a) / (d * &n pow b)) --> &0`,
(* {{{ Proof *)
[
  STRIP_TAC THEN STRIP_TAC;
  INDUCT_TAC;
  REPEAT STRIP_TAC;
  REWRITE_TAC[real_pow;REAL_MUL_RID];
  POP_ASSUM MP_TAC THEN MATCH_ACCEPT_TAC LIM_INV_CON;
  REPEAT STRIP_TAC;
  REWRITE_TAC[real_pow];
  CLAIM `(b = SUC(PRE b))`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ONCE_ASM_REWRITE_TAC[];
  REWRITE_TAC[real_pow];
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c`];
  ONCE_REWRITE_TAC[REAL_DIV_DISTRIB_2];
  ONCE_REWRITE_TAC[REAL_ARITH `&0 = &1 * &0`];
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC;
  MATCH_ACCEPT_TAC LIM_NN;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC;
  ARITH_TAC;
]);;
(* }}} *)

let LIM_POLY_LT = prove_by_refinement(
  `!p k. LENGTH p <= k ==> (\n. poly p (&n) / &n pow k) --> &0`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[poly;LENGTH];
  REPEAT STRIP_TAC;
  REWRITE_TAC[REAL_DIV_LZERO;SEQ_CONST];
  REWRITE_TAC[poly;LENGTH];
  REPEAT STRIP_TAC;
  CLAIM `~(k = 0)`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  LABEL_ALL_TAC;
  CLAIM `LENGTH t <= PRE k`;
  USE_THEN "Z-1" MP_TAC THEN ARITH_TAC;
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  STRIP_TAC;
  REWRITE_TAC[REAL_DIV_ADD_DISTRIB];
  ONCE_REWRITE_TAC[REAL_ARITH `&0 = &0 + &0`];
  MATCH_MP_TAC SEQ_ADD;
  CONJ_TAC;
  ONCE_REWRITE_TAC[ARITH_RULE `n pow k = &1 * n pow k`];
  MATCH_MP_TAC LIM_INV_CON;
  USE_THEN "Z-0" MP_TAC THEN ARITH_TAC;
  CLAIM `k = SUC (PRE k)`;
  USE_THEN "Z-0" MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ONCE_ASM_REWRITE_TAC[];
  REWRITE_TAC[real_pow];
  REWRITE_TAC[REAL_DIV_DISTRIB_2];
  ONCE_REWRITE_TAC[REAL_ARITH `&0 = &1 * &0`];
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC;
  MATCH_ACCEPT_TAC LIM_NN;
  FIRST_ASSUM MATCH_MP_TAC;
  USE_THEN "Z-1" MP_TAC THEN ARITH_TAC;
]);;

(* }}} *)

let LIM_POLY = prove_by_refinement(
  `!p. (0 < LENGTH p /\ ~(LAST p = &0)) ==>
     (\n. poly p (&n) / (LAST p * &n pow PRE (LENGTH p))) --> &1`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH;LT];
  ASM_REWRITE_TAC[LENGTH;poly];
  REPEAT STRIP_TAC;
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[PRE;real_pow;REAL_POW_1;LAST;poly;REAL_MUL_RZERO;REAL_ADD_RID;LENGTH;REAL_DIV_DISTRIB_L];
  CLAIM `~(h = &0)`;
  ASM_MESON_TAC[LAST];
  STRIP_TAC;
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[REAL_ARITH `&1 = &1 * &1`]));
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC;
  ASM_SIMP_TAC[DIV_ID];
  MATCH_ACCEPT_TAC SEQ_CONST;
  ASM_SIMP_TAC[DIV_ID;REAL_10];
  MATCH_ACCEPT_TAC SEQ_CONST;
  CLAIM `LAST (CONS h t) = LAST t`;
  ASM_REWRITE_TAC[LAST];
  STRIP_TAC;
  ASM_REWRITE_TAC[LAST;PRE];
  REWRITE_TAC[REAL_DIV_ADD_DISTRIB];
  ONCE_REWRITE_TAC [REAL_ARITH `&1 = &0 + &1`];
  MATCH_MP_TAC SEQ_ADD;
  CLAIM `~(LENGTH t = 0)`;
  ASM_MESON_TAC[LENGTH_0];
  STRIP_TAC;
  CONJ_TAC;
  MATCH_MP_TAC LIM_INV_CON;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  CLAIM `(LENGTH t = SUC (PRE (LENGTH t)))`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ONCE_ASM_REWRITE_TAC[];
  REWRITE_TAC[real_pow];
  ONCE_REWRITE_TAC[ARITH_RULE `a * b * c = b * a * c`];
  REWRITE_TAC[REAL_DIV_DISTRIB_2];
  ONCE_REWRITE_TAC [REAL_ARITH `&1 = &1 * &1`];
  MATCH_MP_TAC SEQ_MUL;
  CONJ_TAC;
  MATCH_ACCEPT_TAC LIM_NN;
  FIRST_ASSUM MATCH_MP_TAC;
  CONJ_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN ARITH_TAC;
  ASM_MESON_TAC[];
]);;

(* }}} *)

let mono_inc = new_definition(
  `mono_inc (f:num -> real) = !(m:num) n. m <= n ==> f m <= f n`);;

let mono_dec = new_definition(
  `mono_dec (f:num -> real) = !(m:num) n. m <= n ==> f n <= f m`);;

let mono_inc_dec = prove_by_refinement(
  `!f. mono f <=> mono_inc f \/ mono_dec f`,
(* {{{ Proof *)
[
  REWRITE_TAC[mono_inc;mono_dec;mono;real_ge]
]);;
(* }}} *)

let mono_inc_pow = prove_by_refinement(
 `!k. mono_inc (\n. &n pow k)`,
(* {{{ Proof *)

[
  REWRITE_TAC[mono_inc];
  INDUCT_TAC THEN REWRITE_TAC[real_pow;REAL_LE_REFL];
  GEN_TAC THEN GEN_TAC;
  DISCH_THEN (fun x -> (RULE_ASSUM_TAC (fun y -> MATCH_MP y x)) THEN ASSUME_TAC x);
  MATCH_MP_TAC REAL_LE_MUL2;
  REPEAT STRIP_TAC;
  MATCH_ACCEPT_TAC REAL_NUM_LE_0;
  ASM_REWRITE_TAC[REAL_LE];
  MATCH_MP_TAC REAL_POW_LE;
  MATCH_ACCEPT_TAC REAL_NUM_LE_0;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;

(* }}} *)

let mono_inc_pow_const = prove_by_refinement(
 `!k c. &0 < c ==> mono_inc (\n. c * &n pow k)`,
(* {{{ Proof *)

[
  REWRITE_TAC[mono_inc];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC REAL_LE_MUL2;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_LE];
  REAL_ARITH_TAC;
  MATCH_MP_TAC REAL_POW_LE;
  MATCH_ACCEPT_TAC REAL_NUM_LE_0;
  ASM_MESON_TAC[mono_inc_pow;mono_inc]
]);;

(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  Unbounded sequences                                                   *)
(* ---------------------------------------------------------------------- *)

let mono_unbounded_above = new_definition(
 `mono_unbounded_above (f:num -> real) = !c. ?N. !n. N <= n ==> c < f n`);;

let mono_unbounded_below = new_definition(
 `mono_unbounded_below (f:num -> real) = !c. ?N. !n. N <= n ==> f n < c`);;

let mono_unbounded_above_pos = prove_by_refinement(
 `mono_unbounded_above (f:num -> real) = !c. &0 <= c ==> ?N. !n. N <= n ==> c < f n`,
(* {{{ Proof *)
[
  REWRITE_TAC[mono_unbounded_above];
  EQ_TAC THENL [ASM_MESON_TAC[];ALL_TAC];
  REPEAT STRIP_TAC;
  POP_ASSUM (ASSUME_TAC o ISPEC `abs c`);
  POP_ASSUM (MP_TAC o (C MATCH_MP) (ISPEC `c:real` ABS_POS));
  STRIP_TAC;
  EXISTS_TAC `N`;
  GEN_TAC;
  DISCH_THEN (fun x -> POP_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x)));
  ASM_MESON_TAC[ABS_LE;REAL_LET_TRANS];
]);;
(* }}} *)

let mono_unbounded_below_neg = prove_by_refinement(
 `mono_unbounded_below (f:num -> real) = !c. c <= &0 ==> ?N. !n. N <= n ==> f n < c`,
(* {{{ Proof *)
[
  REWRITE_TAC[mono_unbounded_below];
  EQ_TAC THENL [ASM_MESON_TAC[];ALL_TAC];
  REPEAT STRIP_TAC;
  POP_ASSUM (ASSUME_TAC o ISPEC `-- (abs c)`);
  POP_ASSUM (MP_TAC o (C MATCH_MP) (ISPEC `c:real` NEG_ABS));
  STRIP_TAC;
  EXISTS_TAC `N`;
  GEN_TAC;
  DISCH_THEN (fun x -> POP_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x)));
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let mua_quotient_limit = prove_by_refinement(
 `!k f g. &0 < k /\ (\n. f n / g n) --> k /\ mono_unbounded_above g
    ==> mono_unbounded_above f`,
(* {{{ Proof *)
[
  REWRITE_TAC[SEQ;mono_unbounded_above_pos;AND_IMP_THM];
  REPEAT GEN_TAC;
  STRIP_TAC;
  CLAIM `&0 < k / &2`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  DISCH_THEN (fun x -> DISCH_THEN (fun y -> (ASSUME_TAC (MATCH_MP (ISPEC `k / &2` y) x))));
  POP_ASSUM (X_CHOOSE_TAC `M:num`);
  STRIP_TAC;
  X_GEN_TAC `d:real`;
  STRIP_TAC;
  CLAIM `&0 <= &2 * d / k`;
  MATCH_MP_TAC REAL_LE_MUL;
  CONJ_TAC THENL [REAL_ARITH_TAC;ALL_TAC];
  MATCH_MP_TAC REAL_LE_DIV;
  CONJ_TAC THENL [FIRST_ASSUM MATCH_ACCEPT_TAC;ASM_MESON_TAC[REAL_LT_LE]];
  STRIP_TAC;
  LABEL_ALL_TAC;
  MOVE_TO_FRONT "Z-2";
  POP_ASSUM (fun x -> USE_THEN "Z-0" (fun y -> MP_TAC (MATCH_MP x y)));
  DISCH_THEN (X_CHOOSE_TAC `K:num`);
  EXISTS_TAC `nmax M K`;
  REPEAT STRIP_TAC;
  CLAIM `M <= n /\ K <= (n:num)`;
  POP_ASSUM MP_TAC THEN REWRITE_TAC[nmax] THEN COND_CASES_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  RULE_ASSUM_TAC (REWRITE_RULE[GE]);
  FIRST_X_ASSUM (fun x -> FIRST_X_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x)));
  FIRST_X_ASSUM (fun x -> FIRST_X_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x)));
  RULE_ASSUM_TAC (REWRITE_RULE[real_div]);
  CASES_ON `k <= f n * inv (g n)`;
  MATCH_MP_TAC (prove(`d <= &2 * d /\ &2 * d < k * (g n) /\ k * (g n) <= f n ==> d < f n`,MESON_TAC !REAL_REWRITES));
  REPEAT STRIP_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  FIRST_ASSUM (fun x -> ASSUME_TAC (MATCH_MP (REWRITE_RULE[AND_IMP_THM] REAL_LT_LMUL) x));
  LABEL_ALL_TAC;
  POP_ASSUM (fun y -> USE_THEN "Z-6" (fun x -> ASSUME_TAC (MATCH_MP y x)));
  CLAIM `k * &2 * d * inv k = (k * inv k) * &2 * d`;
  REAL_ARITH_TAC;
  CLAIM `k * inv k = &1`;
  ASM_MESON_TAC[REAL_MUL_RINV;REAL_LT_NZ];
  STRIP_TAC;
  ASM_REWRITE_TAC[REAL_MUL_LID];
  ASM_MESON_TAC[];
  (* *)
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP;
  EXISTS_TAC `inv (g n)`;
  REWRITE_TAC[GSYM REAL_MUL_ASSOC];
  CLAIM `&0 < inv (g n)`;
  CLAIM `&0 < inv k`;
  MATCH_MP_TAC REAL_LT_INV THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  CLAIM `&0 < g n`;
  ASM_MESON_TAC !REAL_REWRITES;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_INV];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `g n * inv (g n) = &1`;
  ASM_MESON_TAC[REAL_MUL_RINV;REAL_LT_NZ;REAL_LT_INV_EQ];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[REAL_MUL_RID];
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  (* *)
  RULE_ASSUM_TAC (REWRITE_RULE[REAL_NOT_LE]);
  CLAIM `f n * inv (g n) - k < &0`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `abs (f n * inv (g n) - k) = k - (f n * inv (g n))`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  DISCH_THEN (RULE_ASSUM_TAC o REWRITE_RULE o list);
  CLAIM `k * inv(&2) < f n * inv (g n)`;
  LABEL_ALL_TAC;
  USE_THEN "Z-5" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `k * g n < &2 * f n`;
  CLAIM `&0 < g n`;
  LABEL_ALL_TAC;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `&2 * d * inv k`;
  CONJ_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP;
  EXISTS_TAC `inv(&2)`;
  CONJ_TAC THENL [REAL_ARITH_TAC;ALL_TAC];
  REWRITE_TAC[ARITH_RULE `inv(&2) * &2 = &1`;REAL_MUL_LID;REAL_MUL_ASSOC];
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP;
  EXISTS_TAC `inv(g n)`;
  CONJ_TAC;
  ASM_MESON_TAC[REAL_LT_INV];
  ONCE_REWRITE_TAC[ARITH_RULE `a * (b * c) * d = c * b * (d * a)`];
  CLAIM `g n * inv (g n) = &1`;
  POP_ASSUM MP_TAC THEN ASM_MESON_TAC[REAL_MUL_RINV;REAL_POS_NZ];
  DISCH_THEN SUBST1_TAC;
  ASM_MESON_TAC[REAL_MUL_RID;REAL_MUL_SYM];
  STRIP_TAC;
  CLAIM `&2 * d < k * g n`;
  MATCH_MP_TAC REAL_LT_RCANCEL_IMP;
  EXISTS_TAC `inv k`;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_LT_INV];
  MATCH_MP_TAC REAL_LTE_TRANS;
  EXISTS_TAC `g n`;
  CONJ_TAC;
  REWRITE_TAC[GSYM REAL_MUL_ASSOC];
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  LABEL_ALL_TAC;
  ONCE_REWRITE_TAC[ARITH_RULE `(a * b) * c = b * (a * c)`];
  CLAIM `k * inv k = &1`;
  ASM_MESON_TAC[REAL_MUL_RINV;REAL_POS_NZ];
  DISCH_THEN SUBST1_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&2 * d < &2 * f n`;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REAL_ARITH_TAC;
]);;
(* }}} *)

let mua_neg = prove_by_refinement(
 `!f. mono_unbounded_above f = mono_unbounded_below (\n. -- (f n))`,
(* {{{ Proof *)

[
  MESON_TAC[mono_unbounded_above;mono_unbounded_below;REAL_ARITH `x < y ==> --y < -- x`;REAL_ARITH `-- (-- x) = x`];
]);;

(* }}} *)

let mua_neg2 = prove_by_refinement(
 `!f. mono_unbounded_below f = mono_unbounded_above (\n. -- (f n))`,
(* {{{ Proof *)
[
  MESON_TAC[mono_unbounded_above;mono_unbounded_below;REAL_ARITH `x < y ==> --y < -- x`;REAL_ARITH `-- (-- x) = x`];
]);;
(* }}} *)

let mua_quotient_limit_neg = prove_by_refinement(
 `!k f g. &0 < k /\ (\n. f n / g n) --> k /\ mono_unbounded_below g
    ==> mono_unbounded_below f`,
(* {{{ Proof *)

[
  REWRITE_TAC[mua_neg2];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC (mua_quotient_limit);
  EXISTS_TAC `k`;
  EXISTS_TAC `\n. -- g n`;
  ASM_REWRITE_TAC[];
  POP_ASSUM (fun x -> ALL_TAC);
  POP_ASSUM MP_TAC;
  REWRITE_TAC[SEQ];
  DISCH_THEN (fun x -> REPEAT STRIP_TAC THEN MP_TAC x);
  DISCH_THEN (MP_TAC o ISPEC `e:real`);
  ANTS_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  EXISTS_TAC `N`;
  REPEAT STRIP_TAC;
  REWRITE_TAC[real_div;REAL_NEG_MUL2;REAL_INV_NEG];
  ASM_MESON_TAC[real_div];
]);;

(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  Polynomial properties                                                 *)
(* ---------------------------------------------------------------------- *)

let normal = new_definition(
 `normal p <=> ((normalize p = p) /\ ~(p = []))`);;

let nonconstant = new_definition(
 `nonconstant p <=> normal p /\ (!x. ~(p = [x]))`);;

let degree = new_definition
  `degree p = PRE(LENGTH(normalize p))`;;

let NORMALIZE_SING = prove_by_refinement(
  `!x. (normalize [x] = [x]) <=> ~(x = &0)`,
(* {{{ Proof *)
[
  MESON_TAC[NOT_CONS_NIL;normalize];
]);;
(* }}} *)

let NORMALIZE_PAIR = prove_by_refinement(
  `!x y. ~(y = &0) <=> (normalize [x; y] = [x; y])`,
(* {{{ Proof *)
[
  REWRITE_TAC[normalize;NOT_CONS_NIL];
  REPEAT GEN_TAC;
  COND_CASES_TAC;
  CLAIM `y = &0`;
  ASM_MESON_TAC !LIST_REWRITES;
  DISCH_THEN SUBST1_TAC;
  ASM_MESON_TAC !LIST_REWRITES;
  ASM_MESON_TAC !LIST_REWRITES;
]);;
(* }}} *)

let POLY_NORMALIZE = prove
 (`!p. poly (normalize p) = poly p`,
(* {{{ Proof *)
  LIST_INDUCT_TAC THEN REWRITE_TAC[normalize; poly] THEN
  ASM_CASES_TAC `h = &0` THEN ASM_REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[poly; FUN_EQ_THM] THEN
  UNDISCH_TAC `poly (normalize t) = poly t` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[poly] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_ADD_LID]);;
(* }}} *)

let NORMAL_CONS = prove_by_refinement(
 `!h t. normal t ==> normal (CONS h t)`,
 (* {{{ Proof *)
[
  REWRITE_TAC[normal;normalize];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[NOT_CONS_NIL];
]);;
(* }}} *)

let NORMAL_TAIL = prove_by_refinement(
 `!h t. ~(t = []) /\ normal (CONS h t) ==> normal t`,
(* {{{ Proof *)
[
  REWRITE_TAC[normal;normalize];
  REPEAT STRIP_TAC  THENL [ALL_TAC;ASM_MESON_TAC[]];
  CASES_ON `normalize t = []`;
  ASM_MESON_TAC[NOT_CONS_NIL;CONS_11];
  ASM_MESON_TAC[NOT_CONS_NIL;CONS_11];
]);;
(* }}} *)

let NORMAL_LAST_NONZERO = prove_by_refinement(
 `!p. normal p ==> ~(LAST p = &0)`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  ASM_MESON_TAC[normal];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[normal;normalize;NOT_CONS_NIL;LAST];
  MESON_TAC[NOT_CONS_NIL];
  ASM_SIMP_TAC[GSYM LAST_CONS];
  ASM_REWRITE_TAC[LAST;NOT_CONS_NIL;];
  STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_MESON_TAC[];
]);;

(* }}} *)

let NORMAL_LENGTH = prove_by_refinement(
  `!p. normal p ==> 0 < LENGTH p`,
(* {{{ Proof *)

[
  MESON_TAC[normal;LENGTH_0;ARITH_RULE `~(n = 0) <=> 0 < n`]
]);;

(* }}} *)

let NORMAL_LAST_LENGTH = prove_by_refinement(
  `!p. 0 < LENGTH p /\ ~(LAST p = &0) ==> normal p`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  MESON_TAC[LENGTH;LT_REFL];
  STRIP_TAC;
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[normal;NORMALIZE_SING;NOT_CONS_NIL;];
  ASM_MESON_TAC[LAST];
  MATCH_MP_TAC NORMAL_CONS;
  FIRST_ASSUM MATCH_MP_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[LENGTH_0;ARITH_RULE `~(n = 0) <=> 0 < n`];
  ASM_MESON_TAC[LAST_CONS];
]);;

(* }}} *)

let NORMAL_ID = prove_by_refinement(
 `!p. normal p <=> 0 < LENGTH p /\ ~(LAST p = &0)`,
(* {{{ Proof *)
[
  MESON_TAC[NORMAL_LAST_LENGTH;NORMAL_LENGTH;NORMAL_LAST_NONZERO];
]);;
(* }}} *)

let LIM_POLY2 = prove_by_refinement(
  `!p. normal p ==> (\n. poly p (&n) / (LAST p * &n pow (degree p))) --> &1`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[degree];
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[normal];
  DISCH_THEN SUBST1_TAC;
  MATCH_MP_TAC LIM_POLY;
  ASM_MESON_TAC[NORMAL_ID];
]);;

(* }}} *)

let POW_UNB = prove_by_refinement(
  `!k. 0 < k ==> mono_unbounded_above (\n. (&n) pow k)`,
(* {{{ Proof *)

[
  REWRITE_TAC[mono_unbounded_above];
  REPEAT STRIP_TAC;
  MP_TAC (ISPEC `max (&1) c` REAL_ARCH_SIMPLE_LT);
  STRIP_TAC;
  EXISTS_TAC `n`;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC REAL_LTE_TRANS;
  EXISTS_TAC `&n`;
  CONJ_TAC;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `max (&1) c`;
  ASM_MESON_TAC[REAL_MAX_MAX];
  MATCH_MP_TAC REAL_LE_TRANS;
  EXISTS_TAC `&n'`;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_LE];
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[REAL_ARITH `x = x pow 1`]));
  MATCH_MP_TAC REAL_POW_MONO;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LE_TRANS;
  EXISTS_TAC `max (&1) c`;
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_MAX_MAX];ALL_TAC];
  MATCH_MP_TAC REAL_LE_TRANS;
  EXISTS_TAC `&n`;
  ASM_MESON_TAC (!REAL_REWRITES @ [REAL_LE;REAL_LT_LE]);
  EVERY_ASSUM MP_TAC THEN ARITH_TAC;
]);;

(* }}} *)

let POW_UNB_CON = prove_by_refinement(
  `!k a. 0 < k /\ &0 < a ==> mono_unbounded_above (\n. a * (&n) pow k)`,
(* {{{ Proof *)

[
  REWRITE_TAC[mono_unbounded_above;AND_IMP_THM;];
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  MOVE_TO_FRONT "Z-1";
  POP_ASSUM (fun x ->  MP_TAC (MATCH_MP POW_UNB x));
  REWRITE_TAC[mono_unbounded_above];
  DISCH_THEN (MP_TAC o ISPEC `inv a * c`);
  STRIP_TAC;
  EXISTS_TAC `N`;
  STRIP_TAC;
  DISCH_THEN (fun x -> POP_ASSUM (fun y -> ASSUME_TAC (MATCH_MP  y x)));
  CLAIM `inv a * a = &1`;
  MATCH_MP_TAC REAL_MUL_LINV;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_LCANCEL_IMP;
  EXISTS_TAC `inv a`;
  CONJ_TAC;
  ASM_MESON_TAC[REAL_LT_INV];
  ASM_REWRITE_TAC[REAL_MUL_ASSOC;REAL_MUL_LID];
]);;

(* }}} *)

let POW_UNBB_CON = prove_by_refinement(
  `!k a. 0 < k /\ a < &0 ==> mono_unbounded_below (\n. a * (&n) pow k)`,
(* {{{ Proof *)

[
  REWRITE_TAC[mua_neg2;ARITH_RULE `--(x * y) = -- x * y`];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC POW_UNB_CON;
  STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;

(* }}} *)

let POLY_SING = prove_by_refinement(
  `!x y. poly [x] y = x`,
(* {{{ Proof *)
[
  REWRITE_TAC[poly];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_LAST_GT = prove_by_refinement(
  `!p. normal p /\ (?X. !x. X < x ==> &0 < poly p x) ==> &0 < LAST p`,
(* {{{ Proof *)

[
  GEN_TAC;
  CASES_ON `LENGTH p = 1`;
  RULE_ASSUM_TAC (REWRITE_RULE[LENGTH_1]);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[LAST_SING;POLY_SING];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  EXISTS_TAC `X + &1`;
  REAL_ARITH_TAC;
  (* *)
  REWRITE_TAC[AND_IMP_THM;];
  DISCH_THEN (fun x -> MP_TAC (MATCH_MP LIM_POLY2 x) THEN ASSUME_TAC x);
  REPEAT STRIP_TAC;
  DISJ_CASES_TAC (ISPECL [`&0`;`LAST (p:real list)`] REAL_LT_TOTAL);
  ASM_MESON_TAC[NORMAL_ID];
  POP_ASSUM DISJ_CASES_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  (* save *)
  CLAIM `mono_unbounded_below (\n. LAST p * &n pow degree p)`;
  MATCH_MP_TAC POW_UNBB_CON;
  REWRITE_TAC[degree];
  CONJ_TAC THENL [ALL_TAC;FIRST_ASSUM MATCH_ACCEPT_TAC];
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[normal];
  DISCH_THEN SUBST1_TAC;
  CLAIM `~(LENGTH p = 0)`;
  ASM_MESON_TAC[normal;LENGTH_EQ_NIL];
  LABEL_ALL_TAC;
  USE_THEN "Z-4" MP_TAC;
  ARITH_TAC;
  (* save *)
  STRIP_TAC;
  CLAIM `mono_unbounded_below (\n. poly p (&n))`;
  MATCH_MP_TAC mua_quotient_limit_neg;
  BETA_TAC;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. LAST p * &n pow degree p)`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  BETA_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  REWRITE_TAC[mono_unbounded_below];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM_LIST (fun x -> ALL_TAC);
  MP_TAC (ISPEC `X:real` REAL_ARCH_SIMPLE);
  STRIP_TAC;
  DISCH_THEN (ASSUME_TAC o ISPEC `1 + nmax N n`);
  DISCH_THEN (ASSUME_TAC o ISPEC `&1 + &(nmax N n)`);
  POP_ASSUM MP_TAC THEN ANTS_TAC;
  REWRITE_TAC[nmax];
  COND_CASES_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (REWRITE_RULE[NOT_LE;GSYM REAL_LT]);
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  POP_ASSUM MP_TAC THEN ANTS_TAC;
  REWRITE_TAC[nmax];
  ARITH_TAC;
  ASM_MESON_TAC[ARITH_RULE `~(x < y /\ y < x)`;GSYM REAL_OF_NUM_ADD];
]);;

(* }}} *)

let POLY_LAST_LT = prove_by_refinement(
  `!p. normal p /\ (?X. !x. X < x ==> poly p x < &0) ==> LAST p < &0`,
(* {{{ Proof *)

[
  GEN_TAC;
  CASES_ON `LENGTH p = 1`;
  RULE_ASSUM_TAC (REWRITE_RULE[LENGTH_1]);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[LAST_SING;POLY_SING];
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  EXISTS_TAC `X + &1`;
  REAL_ARITH_TAC;
  (* *)
  REWRITE_TAC[AND_IMP_THM;];
  DISCH_THEN (fun x -> MP_TAC (MATCH_MP LIM_POLY2 x) THEN ASSUME_TAC x);
  REPEAT STRIP_TAC;
  DISJ_CASES_TAC (ISPECL [`&0`;`LAST (p:real list)`] REAL_LT_TOTAL);
  ASM_MESON_TAC[NORMAL_ID];
  POP_ASSUM DISJ_CASES_TAC THENL [ALL_TAC;FIRST_ASSUM MATCH_ACCEPT_TAC];
  (* save *)
  CLAIM `mono_unbounded_above (\n. LAST p * &n pow degree p)`;
  MATCH_MP_TAC POW_UNB_CON;
  REWRITE_TAC[degree];
  CONJ_TAC THENL [ALL_TAC;FIRST_ASSUM MATCH_ACCEPT_TAC];
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[normal];
  DISCH_THEN SUBST1_TAC;
  CLAIM `~(LENGTH p = 0)`;
  ASM_MESON_TAC[normal;LENGTH_EQ_NIL];
  LABEL_ALL_TAC;
  USE_THEN "Z-4" MP_TAC;
  ARITH_TAC;
  (* save *)
  STRIP_TAC;
  CLAIM `mono_unbounded_above (\n. poly p (&n))`;
  MATCH_MP_TAC mua_quotient_limit;
  BETA_TAC;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. LAST p * &n pow degree p)`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  BETA_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  REWRITE_TAC[mono_unbounded_above];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM_LIST (fun x -> ALL_TAC);
  MP_TAC (ISPEC `X:real` REAL_ARCH_SIMPLE);
  STRIP_TAC;
  DISCH_THEN (ASSUME_TAC o ISPEC `1 + nmax N n`);
  DISCH_THEN (ASSUME_TAC o ISPEC `&1 + &(nmax N n)`);
  POP_ASSUM MP_TAC THEN ANTS_TAC;
  REWRITE_TAC[nmax];
  COND_CASES_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (REWRITE_RULE[NOT_LE;GSYM REAL_LT]);
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  POP_ASSUM MP_TAC THEN ANTS_TAC;
  REWRITE_TAC[nmax];
  ARITH_TAC;
  ASM_MESON_TAC[ARITH_RULE `~(x < y /\ y < x)`;GSYM REAL_OF_NUM_ADD];
]);;

(* }}} *)

let NORMALIZE_LENGTH_MONO = prove_by_refinement(
  `!l. LENGTH (normalize l) <= LENGTH l`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  MESON_TAC[normalize;LE_REFL];
  REWRITE_TAC[LENGTH;normalize];
  REPEAT COND_CASES_TAC THEN REWRITE_TAC[LENGTH] THEN EVERY_ASSUM MP_TAC THEN ARITH_TAC;
]);;
(* }}} *)

let DEGREE_SING = prove_by_refinement(
  `!x. (degree [x] = 0)`,
(* {{{ Proof *)
[
  REWRITE_TAC[degree];
  STRIP_TAC;
  CASES_ON `x = &0`;
  ASM_REWRITE_TAC[normalize;LENGTH];
  ARITH_TAC;
  CLAIM `normalize [x] = [x]`;
  ASM_MESON_TAC[NORMALIZE_SING];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
]);;
(* }}} *)

let DEGREE_CONS = prove_by_refinement(
  `!h t. normal t ==> (degree (CONS h t) = 1 + degree t)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  CLAIM `normal (CONS h t)`;
  ASM_MESON_TAC[NORMAL_CONS];
  REWRITE_TAC[normal;degree];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  RULE_ASSUM_TAC (REWRITE_RULE[normal]);
  CLAIM `~(LENGTH t = 0)`;
  ASM_MESON_TAC[LENGTH_0];
  STRIP_TAC;
  ASM_REWRITE_TAC[LENGTH];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
]);;

(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  Now the derivative                                                    *)
(* ---------------------------------------------------------------------- *)

let PDA_LENGTH = prove_by_refinement(
 `!p n. ~(p = []) ==> (LENGTH(poly_diff_aux n p) = LENGTH p)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  GEN_TAC THEN DISCH_THEN IGNORE;
  REWRITE_TAC[LENGTH;poly_diff_aux;];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[LENGTH;poly_diff_aux;];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let POLY_DIFF_LENGTH = prove_by_refinement(
 `!p. LENGTH (poly_diff p) = PRE (LENGTH p)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[poly_diff;LENGTH;PRE];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[LENGTH;PRE];
  REWRITE_TAC[poly_diff;NOT_CONS_NIL;TL;PRE;poly_diff_aux;LENGTH;];
  REWRITE_TAC[poly_diff;TL;LENGTH;PRE;NOT_CONS_NIL;];
  MATCH_MP_TAC PDA_LENGTH;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let POLY_DIFF_SING = prove_by_refinement(
 `!p h. (poly_diff p = [h]) <=> ?x. p = [x; h]`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `LENGTH (p:real list)` (ARITH_RULE `!n. (n = 0) \/ (n = 1) \/ (n = 2) \/ 2 < n`));
  ASM_MESON_TAC[poly_diff;LENGTH_0;NOT_CONS_NIL;];
  POP_ASSUM DISJ_CASES_TAC;
  RULE_ASSUM_TAC (REWRITE_RULE[LENGTH_1]);
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN POP_ASSUM SUBST1_TAC;
  REWRITE_TAC[poly_diff;NOT_CONS_NIL;TL;poly_diff_aux;];
  ASM_MESON_TAC !LIST_REWRITES;
  POP_ASSUM DISJ_CASES_TAC;
  RULE_ASSUM_TAC (MATCH_EQ_MP LENGTH_PAIR);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[poly_diff;NOT_CONS_NIL;TL;poly_diff_aux;REAL_MUL_LID;];
  ASM_MESON_TAC[CONS_11];
  EQ_TAC;
  STRIP_TAC;
  POP_ASSUM (ASSUME_TAC o (AP_TERM `LENGTH:((real) list) -> num`));
  RULE_ASSUM_TAC(REWRITE_RULE[LENGTH]);
  CLAIM `PRE (LENGTH p) = 1`;
  ASM_MESON_TAC[POLY_DIFF_LENGTH;ARITH_RULE `SUC 0 = 1`];
  STRIP_TAC;
  CLAIM `LENGTH p = 2`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  ASM_MESON_TAC[LT_REFL];
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[poly_diff;NOT_CONS_NIL;TL;poly_diff_aux;REAL_MUL_LID;];
]);;
(* }}} *)

let lem = prove_by_refinement(
  `!p n. ~(p = []) ==> (LAST (poly_diff_aux n p) = LAST p * &(PRE(LENGTH p) + n))`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  REPEAT STRIP_TAC;
  POP_ASSUM IGNORE;
  REWRITE_TAC[LENGTH;poly_diff_aux;];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[poly_diff_aux;LAST;LENGTH;GSYM REAL_OF_NUM_ADD];
  CLAIM `((SUC 0) - 1) + n = n`;
  ARITH_TAC;
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[PRE];
  REAL_ARITH_TAC;
  POP_ASSUM (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)) THEN ASSUME_TAC x);
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  LIST_SIMP_TAC;
  ASM_REWRITE_TAC[];
  COND_CASES_TAC;
  REWRITE_TAC[PRE];
  ASM_MESON_TAC[PDA_LENGTH;LENGTH;LENGTH_0];
  REWRITE_TAC[PRE];
  MATCH_EQ_MP_TAC (GSYM REAL_EQ_MUL_LCANCEL);
  DISJ2_TAC;
  AP_TERM_TAC;
  CLAIM `~(LENGTH t = 0)`;
  ASM_MESON_TAC[LENGTH_0];
  ARITH_TAC;
]);;

(* }}} *)

let NONCONSTANT_LENGTH = prove_by_refinement(
  `!p. nonconstant p ==> 1 < LENGTH p`,
(* {{{ Proof *)

[
  REWRITE_TAC[nonconstant;normal];
  ASM_MESON_TAC[LENGTH_0;LENGTH_1;ARITH_RULE `(x = 0) \/ (x = 1) \/ 1 < x`];
]);;

(* }}} *)

let NONCONSTANT_DIFF_NIL = prove_by_refinement(
  `!p. nonconstant p ==> ~(poly_diff p = [])`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `1 < LENGTH p`;
  ASM_MESON_TAC[NONCONSTANT_LENGTH];
  STRIP_TAC;
  CLAIM `0 < LENGTH (poly_diff p)`;
  REWRITE_TAC[POLY_DIFF_LENGTH];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  ASM_REWRITE_TAC[LENGTH];
  ARITH_TAC;
]);;
(* }}} *)

let NONCONSTANT_DEGREE = prove_by_refinement(
  `!p. nonconstant p ==> 0 < degree p`,
(* {{{ Proof *)
[
  GEN_TAC;
  DISCH_THEN (fun x -> ASSUME_TAC x THEN MP_TAC x);
  REWRITE_TAC[nonconstant;degree];
  REPEAT STRIP_TAC;
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[normal];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  CLAIM `1 < LENGTH p`;
  ASM_MESON_TAC[NONCONSTANT_LENGTH];
  ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_LAST_LEM = prove_by_refinement(
  `!p. nonconstant p ==> (LAST (poly_diff p) = LAST p * &(degree p))`,
(* {{{ Proof *)
[
  REWRITE_TAC[nonconstant;poly_diff;];
  REPEAT STRIP_TAC;
  COND_CASES_TAC;
  ASM_MESON_TAC[normal];
  CLAIM `~(TL p = [])`;
  ASM_MESON_TAC[TL;NOT_CONS_NIL;list_CASES;TL_NIL];
  DISCH_THEN (fun x -> MP_TAC (MATCH_MP lem x) THEN ASSUME_TAC x);
  DISCH_THEN (ASSUME_TAC o ISPEC `1`);
  ASM_REWRITE_TAC[];
  CLAIM `LAST (TL p) = LAST p`;
  ASM_MESON_TAC[LAST_TL];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[degree];
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[normal];
  DISCH_THEN SUBST1_TAC;
  MATCH_EQ_MP_TAC (GSYM REAL_EQ_MUL_LCANCEL);
  DISJ2_TAC;
  AP_TERM_TAC;
  ASM_SIMP_TAC[LENGTH_TL];
  CLAIM `~(LENGTH p = 0)`;
  ASM_MESON_TAC[LENGTH_0];
  CLAIM `~(LENGTH p = 1)`;
  ASM_MESON_TAC[LENGTH_1];
  ARITH_TAC;
]);;
(* }}} *)

let NONCONSTANT_DIFF_0 = prove_by_refinement(
  `!p. nonconstant p ==> ~(poly_diff p = [&0])`,
(* {{{ Proof *)

[
  STRIP_TAC;
  DISCH_THEN (fun x -> MP_TAC x THEN ASSUME_TAC x);
  REWRITE_TAC[nonconstant];
  REPEAT STRIP_TAC;
  CLAIM `~(p = [])`;
  ASM_MESON_TAC[normal];
  DISCH_THEN (fun x -> RULE_ASSUM_TAC (REWRITE_RULE[x]) THEN ASSUME_TAC x);
  CLAIM `~(LAST p = &0)`;
  MATCH_MP_TAC NORMAL_LAST_NONZERO;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  CLAIM `LAST p * &(degree p) = &0`;
  ASM_SIMP_TAC[GSYM POLY_DIFF_LAST_LEM];
  REWRITE_TAC[LAST];
  STRIP_TAC;
  CLAIM `(LAST p = &0) \/ (&(degree p) = &0)`;
  ASM_MESON_TAC[REAL_ENTIRE];
  STRIP_TAC;
  ASM_MESON_TAC[];
  CLAIM `?h t. p = CONS h t`;
  ASM_MESON_TAC[list_CASES];
  STRIP_TAC;
  CLAIM `normal t`;
  ASM_MESON_TAC[NORMAL_TAIL];
  STRIP_TAC;
  FIRST_ASSUM (MP_TAC o (MATCH_MP (ISPECL [`h:real`;`t:real list`] DEGREE_CONS)));
  STRIP_TAC;
  CLAIM `degree p = 0`;
  ASM_MESON_TAC [REAL_OF_NUM_EQ];
  ASM_REWRITE_TAC[];
  ARITH_TAC;
]);;

(* }}} *)

let POLY_DIFF_LAST_LT = prove_by_refinement(
 `!p. nonconstant p ==> (LAST (poly_diff p) < &0 <=> LAST p < &0)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ASM_SIMP_TAC[POLY_DIFF_LAST_LEM];
  CLAIM `&0 <= &(degree p)`;
  REAL_ARITH_TAC;
  STRIP_TAC;
  EQ_TAC;
  ASM_MESON_TAC([REAL_MUL_LT] @ !REAL_REWRITES);
  STRIP_TAC;
  CLAIM `0 < degree p`;
  ASM_MESON_TAC[NONCONSTANT_DEGREE];
  STRIP_TAC;
  CLAIM `&0 < &(degree p)`;
  REAL_SIMP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  MATCH_EQ_MP_TAC (GSYM REAL_MUL_LT);
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let POLY_DIFF_LAST_GT = prove_by_refinement(
 `!p. nonconstant p ==> (&0 < LAST (poly_diff p) <=> &0 < LAST p)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ASM_SIMP_TAC[POLY_DIFF_LAST_LEM];
  CLAIM `&0 < &(degree p)`;
  ASM_MESON_TAC[NONCONSTANT_DEGREE;REAL_OF_NUM_LT];
  STRIP_TAC;
  EQ_TAC;
  REWRITE_TAC[REAL_MUL_GT];
  STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  ONCE_REWRITE_TAC [ARITH_RULE `&0 = &0 * &0`];
  MATCH_MP_TAC REAL_LT_MUL2;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let NONCONSTANT_DIFF_NORMAL = prove_by_refinement(
  `!p. nonconstant p ==> normal (poly_diff p)`,
(* {{{ Proof *)
[
  GEN_TAC;
  DISCH_THEN (fun x ->  ASSUME_TAC x THEN MP_TAC x);
  REWRITE_TAC[nonconstant];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC NORMAL_LAST_LENGTH;
  STRIP_TAC;
  CLAIM `1 < LENGTH p`;
  ASM_MESON_TAC[NONCONSTANT_LENGTH];
  STRIP_TAC;
  CLAIM `LENGTH (poly_diff p) = PRE (LENGTH p)`;
  ASM_MESON_TAC[POLY_DIFF_LENGTH];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CASES_ON `LAST p < &0`;
  CLAIM `LAST (poly_diff p) < &0`;
  ASM_MESON_TAC[POLY_DIFF_LAST_LT];
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  REWRITE_ASSUMS !REAL_REWRITES;
  REWRITE_ASSUMS[REAL_LE_LT];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `&0 < LAST (poly_diff p)`;
  ASM_MESON_TAC[POLY_DIFF_LAST_GT];
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  ASM_MESON_TAC[NORMAL_ID];
]);;
(* }}} *)

let PDIFF_POS_LAST = prove_by_refinement(
  `!p. nonconstant p /\ (?X. !x. X < x ==> &0 < poly (poly_diff p) x) ==> &0 < LAST p`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `&0 < LAST (poly_diff p)`;
  MATCH_MP_TAC POLY_LAST_GT;
  ASM_SIMP_TAC[NONCONSTANT_DIFF_NORMAL];
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[GSYM POLY_DIFF_LAST_GT];
]);;
(* }}} *)

let LAST_UNB = prove_by_refinement(
 `!p. nonconstant p /\ &0 < LAST p ==> mono_unbounded_above (\n. poly p (&n))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MATCH_MP_TAC mua_quotient_limit;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. (LAST p) * (&n) pow (degree p))`;
  BETA_TAC;
  STRIP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  MATCH_MP_TAC LIM_POLY2;
  ASM_MESON_TAC[nonconstant];
  MATCH_MP_TAC POW_UNB_CON;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[NONCONSTANT_DEGREE];
]);;
(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  Finally, the positive theorems                                        *)
(* ---------------------------------------------------------------------- *)


let POLY_DIFF_UP_RIGHT = prove_by_refinement(
 `nonconstant p /\ (?X. !x. X < x ==> &0 < poly (poly_diff p) x) ==>
   (?Y. !y. Y < y ==> &0 < poly p y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `mono_unbounded_above (\n. poly p (&n))`;
  MATCH_MP_TAC LAST_UNB;
  ASM_MESON_TAC[PDIFF_POS_LAST];
  REWRITE_TAC[mono_unbounded_above];
  DISCH_THEN (MP_TAC o (ISPEC `&0`));
  STRIP_TAC;
  CLAIM `?K. max X (&N) < &K`;
  ASM_MESON_TAC[REAL_ARCH_SIMPLE_LT];
  STRIP_TAC;
  EXISTS_TAC `&K`;
  REPEAT STRIP_TAC;
  CCONTR_TAC;
  REWRITE_ASSUMS[REAL_NOT_LT];
  CLAIM `&N < y /\ X < y`;
  ASM_MESON_TAC([REAL_MAX_MAX] @ !REAL_REWRITES);
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`&K`;`y:real`] POLY_MVT);
  ANTS_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  CLAIM `poly p y - poly p (&K) <= &0`;
  MATCH_MP_TAC (REAL_ARITH `x <= &0 /\ &0 < y ==> x - y <= &0`);
  ASM_REWRITE_TAC[];
  FIRST_ASSUM MATCH_MP_TAC;
  CLAIM `&N < &K`;
  ASM_MESON_TAC [REAL_MAX_MAX;REAL_LET_TRANS];
  STRIP_TAC;
  CLAIM `N:num < K`;
  ASM_MESON_TAC [REAL_OF_NUM_LT];
  ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - &K`;
  LABEL_ALL_TAC;
  USE_THEN "Z-7" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < poly (poly_diff p) x`;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_MAX_MAX;REAL_LET_TRANS;REAL_LT_TRANS];
  STRIP_TAC;
  CLAIM `&0 < (y - &K) * poly (poly_diff p) x`;
  ONCE_REWRITE_TAC [ARITH_RULE `&0 = &0 * &0`];
  MATCH_MP_TAC REAL_LT_MUL2 THEN REPEAT STRIP_TAC THEN TRY REAL_ARITH_TAC THEN FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  REAL_SOLVE_TAC;
]);;
(* }}} *)

let PDIFF_NEG_LAST = prove_by_refinement(
  `!p. nonconstant p /\ (?X. !x. X < x ==> poly (poly_diff p) x < &0) ==> LAST p < &0`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `LAST (poly_diff p) < &0`;
  MATCH_MP_TAC POLY_LAST_LT;
  ASM_SIMP_TAC[NONCONSTANT_DIFF_NORMAL];
  ASM_MESON_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[GSYM POLY_DIFF_LAST_LT];
]);;
(* }}} *)

let LAST_UNB_NEG = prove_by_refinement(
 `!p. nonconstant p /\ LAST p < &0 ==> mono_unbounded_below (\n. poly p (&n))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MATCH_MP_TAC mua_quotient_limit_neg;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. (LAST p) * (&n) pow (degree p))`;
  BETA_TAC;
  STRIP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  MATCH_MP_TAC LIM_POLY2;
  ASM_MESON_TAC[nonconstant];
  MATCH_MP_TAC POW_UNBB_CON;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[NONCONSTANT_DEGREE];
]);;
(* }}} *)

let POLY_DIFF_DOWN_RIGHT = prove_by_refinement(
 `nonconstant p /\ (?X. !x. X < x ==> poly (poly_diff p) x < &0) ==>
   (?Y. !y. Y < y ==> poly p y < &0)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `mono_unbounded_below (\n. poly p (&n))`;
  MATCH_MP_TAC LAST_UNB_NEG;
  ASM_MESON_TAC[PDIFF_NEG_LAST];
  REWRITE_TAC[mono_unbounded_below];
  DISCH_THEN (MP_TAC o (ISPEC `&0`));
  STRIP_TAC;
  CLAIM `?K. max X (&N) < &K`;
  ASM_MESON_TAC[REAL_ARCH_SIMPLE_LT];
  STRIP_TAC;
  EXISTS_TAC `&K`;
  REPEAT STRIP_TAC;
  CCONTR_TAC;
  REWRITE_ASSUMS[REAL_NOT_LT];
  CLAIM `&N < y /\ X < y`;
  ASM_MESON_TAC([REAL_MAX_MAX] @ !REAL_REWRITES);
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`&K`;`y:real`] POLY_MVT);
  ANTS_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  STRIP_TAC;
  CLAIM `&0 <= poly p y - poly p (&K)`;
  MATCH_MP_TAC (REAL_ARITH `&0 <= x /\ y < &0 ==> &0 <= x - y`);
  ASM_REWRITE_TAC[];
  FIRST_ASSUM MATCH_MP_TAC;
  CLAIM `&N < &K`;
  ASM_MESON_TAC (!REAL_REWRITES @ !NUM_REWRITES);
  STRIP_TAC;
  CLAIM `N:num < K`;
  ASM_MESON_TAC [REAL_OF_NUM_LT];
  ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - &K`;
  LABEL_ALL_TAC;
  USE_THEN "Z-7" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `poly (poly_diff p) x < &0`;
  FIRST_ASSUM MATCH_MP_TAC;
  REAL_SOLVE_TAC;
  STRIP_TAC;
  CLAIM `(y - &K) * poly (poly_diff p) x < &0`;
  ASM_MESON_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  REAL_SOLVE_TAC;
]);;
(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  Now the negative ones                                                 *)
(* ---------------------------------------------------------------------- *)

let UNB_LEFT_EVEN = prove_by_refinement(
 `!k. 0 < k /\ EVEN k ==> mono_unbounded_above (\n. (-- &n) pow k)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ASM_REWRITE_TAC[REAL_POW_NEG];
  MATCH_MP_TAC POW_UNB;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let UNB_LEFT_ODD = prove_by_refinement(
 `!k. 0 < k /\ ODD k ==> mono_unbounded_below (\n. (-- &n) pow k)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS[GSYM NOT_EVEN];
  ASM_REWRITE_TAC[REAL_POW_NEG];
  MATCH_EQ_MP_TAC mua_neg;
  MATCH_MP_TAC POW_UNB;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let EVEN_CONS = prove_by_refinement(
  `!t h. ODD (LENGTH (CONS h t)) = EVEN (LENGTH t)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN
  ASM_MESON_TAC[LENGTH_SING;LENGTH;EVEN;ODD;ONE];
]);;
(* }}} *)

let ODD_CONS = prove_by_refinement(
  `!t h. EVEN (LENGTH (CONS h t)) = ODD (LENGTH t)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN
  ASM_MESON_TAC[LENGTH_SING;LENGTH;EVEN;ODD;ONE];
]);;
(* }}} *)

let MUA_DIV_CONST = prove_by_refinement(
  `!a b p. mono_unbounded_above (\n. p n) ==> (\n. a / (b + p n)) --> &0`,
(* {{{ Proof *)

[
  REWRITE_TAC[mono_unbounded_above;SEQ];
  REPEAT STRIP_TAC;
  REAL_SIMP_TAC;
  CASES_ON `a = &0`;
  ASM_REWRITE_TAC[real_div;REAL_MUL_LZERO;ABS_0];
  ABBREV_TAC `k = (max (&1) (abs a / e - b))`;
  FIRST_ASSUM (MP_TAC o (ISPEC `k:real`));
  STRIP_TAC;
  EXISTS_TAC `N`;
  REPEAT STRIP_TAC;
  REWRITE_ASSUMS (!REAL_REWRITES @ !NUM_REWRITES);
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> ASSUME_TAC (MATCH_MP y x)));
  REWRITE_TAC[REAL_ABS_DIV];
  MATCH_MP_TAC REAL_LTE_TRANS;
  EXISTS_TAC `abs a / (b + k)`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_DIV_DENOM_LT;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ABS_NZ];
  LABEL_ALL_TAC;
  CLAIM `(abs a / e - b) <= k`;
  ASM_MESON_TAC[REAL_MAX_MAX];
  STRIP_TAC;
  CLAIM `&0 < abs a / e`;
  REWRITE_TAC[real_div];
  MATCH_MP_TAC REAL_LT_MUL;
  ASM_MESON_TAC[REAL_INV_POS;REAL_ABS_NZ];
  STRIP_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `-- b < p n`;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `k`;
  ASM_REWRITE_TAC[];
  CLAIM `(abs a / e - b) <= k`;
  ASM_MESON_TAC[REAL_MAX_MAX];
  STRIP_TAC;
  CLAIM `&0 < abs a / e`;
  REWRITE_TAC[real_div];
  MATCH_MP_TAC REAL_LT_MUL;
  ASM_MESON_TAC[REAL_INV_POS;REAL_ABS_NZ];
  STRIP_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `abs (b + p n) = b + p n`;
  MATCH_EQ_MP_TAC REAL_ABS_REFL;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  DISCH_THEN SUBST1_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `(abs a / e - b) <= k`;
  ASM_MESON_TAC[REAL_MAX_MAX];
  STRIP_TAC;
  CLAIM `&0 < abs a / e`;
  REWRITE_TAC[real_div];
  MATCH_MP_TAC REAL_LT_MUL;
  ASM_MESON_TAC[REAL_INV_POS;REAL_ABS_NZ];
  STRIP_TAC;
  LABEL_ALL_TAC;
  CLAIM `abs a / e <= b + k`;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CASES_ON `&1 <= abs a / e - b`;
  CLAIM `k = abs a / e - b`;
  USE_THEN "Z-3" (SUBST1_TAC o GSYM);
  ASM_REWRITE_TAC[real_max];
  ASM_MESON_TAC[real_max];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[ARITH_RULE `b + a - b = a`];
  REWRITE_TAC[real_div;];
  REAL_SIMP_TAC;
  REWRITE_TAC[REAL_MUL_ASSOC];
  CLAIM `~(abs a = &0)`;
  ASM_MESON_TAC[REAL_ABS_NZ;REAL_LT_LE];
  STRIP_TAC;
  ASM_SIMP_TAC[REAL_MUL_RINV];
  REAL_SIMP_TAC;
  (* save *)
  REWRITE_ASSUMS !REAL_REWRITES;
  CLAIM `k = &1`;
  ASM_MESON_TAC([real_max] @ !REAL_REWRITES);
  STRIP_TAC;
  CLAIM `&0 < b + k`;
  MATCH_MP_TAC REAL_LTE_TRANS;
  EXISTS_TAC `abs a / e`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  MATCH_MP_TAC REAL_LE_RCANCEL_IMP;
  EXISTS_TAC `b + k`;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[real_div];
  REWRITE_TAC[GSYM REAL_MUL_ASSOC];
  CLAIM `inv (b + &1) * (b + &1) = &1`;
  LABEL_ALL_TAC;
  POP_ASSUM MP_TAC;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_MESON_TAC[REAL_MUL_LINV;REAL_LT_LE];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[REAL_MUL_RID];
  MATCH_MP_TAC REAL_LE_LCANCEL_IMP;
  EXISTS_TAC `inv e`;
  REPEAT STRIP_TAC;
  USE_THEN "Z-5" MP_TAC;
  MESON_TAC[REAL_INV_POS;REAL_LT_LE];
  REWRITE_TAC[REAL_MUL_ASSOC];
  CLAIM `~(e = &0)`;
  ASM_MESON_TAC[REAL_INV_NZ;REAL_LT_LE];
  STRIP_TAC;
  ASM_SIMP_TAC[REAL_MUL_LINV];
  REAL_SIMP_TAC;
  ASM_MESON_TAC[real_div;REAL_MUL_SYM]
]);;

(* }}} *)

let SEQ_0_NEG = prove_by_refinement(
  `!p. (\n. p n) --> &0 <=> (\n. -- p n) --> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[SEQ];
  GEN_TAC THEN EQ_TAC;
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-0" (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  STRIP_TAC;
  EXISTS_TAC `N`;
  REPEAT STRIP_TAC;
  POP_ASSUM  (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  REAL_SIMP_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ABS_NEG];
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-0" (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  STRIP_TAC;
  EXISTS_TAC `N`;
  REPEAT STRIP_TAC;
  POP_ASSUM  (fun x -> FIRST_ASSUM (fun y -> MP_TAC (MATCH_MP y x)));
  REAL_SIMP_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ABS_NEG];
]);;
(* }}} *)

let lem = prove_by_refinement(
  `!x y z. --(x / (y + z)) = x / (-- y + -- z)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[real_div];
  REWRITE_TAC[ARITH_RULE `--(x * y) = x * -- y`];
  REWRITE_TAC[ARITH_RULE `-- y + -- z = --(y + z)`];
  REWRITE_TAC[REAL_INV_NEG];
]);;
(* }}} *)

let MUB_DIV_CONST = prove_by_refinement(
  `!a b p. mono_unbounded_below (\n. p n) ==> (\n. a / (b + p n)) --> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[mua_neg2];
  REPEAT STRIP_TAC;
  ONCE_REWRITE_TAC[SEQ_0_NEG];
  REWRITE_TAC[lem];
  MATCH_MP_TAC MUA_DIV_CONST;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let mono_unbounded = new_definition(
  `mono_unbounded p <=> mono_unbounded_above p \/ mono_unbounded_below p`);;

let MU_DIV_CONST = prove_by_refinement(
  `!a b p. mono_unbounded p ==> (\n. a / (b + p n)) --> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[mono_unbounded];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC MUA_DIV_CONST;
  REWRITE_TAC[ETA_AX];
  POP_ASSUM MATCH_ACCEPT_TAC;
  MATCH_MP_TAC MUB_DIV_CONST;
  REWRITE_TAC[ETA_AX];
  POP_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let MUA_MUA = prove_by_refinement(
  `!p q. mono_unbounded_above (\n. p n) /\ mono_unbounded_above (\n. q n) ==>
           mono_unbounded_above (\n. p n * q n)`,
(* {{{ Proof *)
[
  REWRITE_TAC[mono_unbounded_above_pos];
  REPEAT STRIP_TAC;
  CLAIM `&0 <= max c (&1)`;
  REWRITE_TAC[real_max];
  COND_CASES_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[];
  DISCH_THEN (fun y -> POP_ASSUM (fun x -> RULE_ASSUM_TAC (C MATCH_MP y) THEN ASSUME_TAC x));
  EVERY_ASSUM MP_TAC THEN REPEAT STRIP_TAC;
  EXISTS_TAC `nmax N N'`;
  REPEAT STRIP_TAC;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `max c (&1)`;
  ASM_REWRITE_TAC[REAL_MAX_MAX];
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `max c (&1) * max c (&1)`;
  REPEAT STRIP_TAC;
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM REAL_MUL_RID]));
  MATCH_MP_TAC REAL_LE_MUL2;
  REPEAT STRIP_TAC;
  REAL_SOLVE_TAC;
  REAL_SIMP_TAC;
  REAL_ARITH_TAC;
  REAL_SOLVE_TAC;
  MATCH_MP_TAC REAL_LT_MUL2;
  REPEAT STRIP_TAC;
  REAL_SOLVE_TAC;
  CLAIM `N <= n /\ N' <= (n:num)`;
  POP_ASSUM MP_TAC;
  REWRITE_TAC[nmax];
  COND_CASES_TAC;
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN ARITH_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  REAL_SOLVE_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REWRITE_TAC[nmax] THEN ARITH_TAC;
]);;
(* }}} *)

let MUA_MUB = prove_by_refinement(
  `!p q. mono_unbounded_above (\n. p n) /\ mono_unbounded_below (\n. q n) ==>
           mono_unbounded_below (\n. p n * q n)`,
(* {{{ Proof *)
[
  REWRITE_TAC[mua_neg2];
  REWRITE_TAC[ARITH_RULE `--(x * y) = x * -- y`];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC MUA_MUA;
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let MUB_MUA = prove_by_refinement(
  `!p q. mono_unbounded_below (\n. p n) /\ mono_unbounded_above (\n. q n) ==>
           mono_unbounded_below (\n. p n * q n)`,
(* {{{ Proof *)
[
  REWRITE_TAC[mua_neg2];
  REWRITE_TAC[ARITH_RULE `--(x * y) = -- x * y`];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC MUA_MUA;
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let MUB_MUB = prove_by_refinement(
  `!p q. mono_unbounded_below (\n. p n) /\ mono_unbounded_below (\n. q n) ==>
           mono_unbounded_above (\n. p n * q n)`,
(* {{{ Proof *)
[
  REWRITE_TAC[mua_neg2];
  ONCE_REWRITE_TAC[ARITH_RULE `(x * y) = -- x * -- y`];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC MUA_MUA;
  ASM_REWRITE_TAC[];
]);;
(* }}} *)

let MU_PROD = prove_by_refinement(
  `!p q. mono_unbounded (\n. p n) /\ mono_unbounded (\n. q n) ==> mono_unbounded (\n. p n * q n)`,
(* {{{ Proof *)
[
  REWRITE_TAC[mono_unbounded];
  ASM_MESON_TAC[MUA_MUA;MUA_MUB;MUB_MUA;MUB_MUB];
]);;
(* }}} *)

let mub_quotient_limit = prove_by_refinement(
 `!k f g. &0 < k /\ (\n. f n / g n) --> k /\ mono_unbounded_below g
    ==> mono_unbounded_below f`,
(* {{{ Proof *)
[
  REWRITE_TAC[mua_neg2];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC mua_quotient_limit;
  EXISTS_TAC `k`;
  EXISTS_TAC `\n. -- g n`;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  BETA_TAC;
  REWRITE_TAC[REAL_NEG_DIV];
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let POLY_UB = prove_by_refinement(
  `!p. nonconstant p ==> mono_unbounded (\n. poly p (&n))`,
(* {{{ Proof *)

[
  GEN_TAC;
  DISCH_THEN (fun x -> ASSUME_TAC x THEN MP_TAC x);
  REWRITE_TAC[nonconstant];
  REPEAT STRIP_TAC;
  FIRST_ASSUM (fun x -> ASSUME_TAC (MATCH_MP LIM_POLY2 x));
  CASES_ON `LAST p < &0`;
  REWRITE_TAC[mono_unbounded];
  DISJ2_TAC;
  MATCH_MP_TAC mub_quotient_limit;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. LAST p * &n pow degree p)`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  BETA_TAC;
  MATCH_MP_TAC LIM_POLY2;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  MATCH_MP_TAC POW_UNBB_CON;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC NONCONSTANT_DEGREE;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  REWRITE_ASSUMS !REAL_REWRITES;
  REWRITE_ASSUMS[REAL_LE_LT];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  (* save *)
  REWRITE_TAC[mono_unbounded];
  DISJ1_TAC;
  MATCH_MP_TAC mua_quotient_limit;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. LAST p * &n pow degree p)`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  BETA_TAC;
  MATCH_MP_TAC LIM_POLY2;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  MATCH_MP_TAC POW_UNB_CON;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC NONCONSTANT_DEGREE;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  ASM_MESON_TAC[NORMAL_LAST_NONZERO];
]);;

(* }}} *)

(* ---------------------------------------------------------------------- *)
(*  A polynomial applied to a negative argument                           *)
(* ---------------------------------------------------------------------- *)

let pneg_aux = new_recursive_definition list_RECURSION
 `(pneg_aux n [] = []) /\
  (pneg_aux n (CONS h t) = CONS (--(&1) pow n * h) (pneg_aux (SUC n) t))`;;

let pneg = new_recursive_definition list_RECURSION
 `(pneg [] = []) /\
  (pneg (CONS h t) = pneg_aux 0 (CONS h t))`;;

let POLY_PNEG_AUX_SUC = prove_by_refinement(
  `!t n. pneg_aux (SUC (SUC n)) t = pneg_aux n t`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  STRIP_TAC;
  REWRITE_TAC[pneg_aux];
  REWRITE_TAC[pneg_aux;pow];
  REAL_SIMP_TAC;
  STRIP_TAC;
  AP_TERM_TAC;
  ASM_MESON_TAC[];
]);;
(* }}} *)

let POLY_NEG_NEG = prove_by_refinement(
 `!p. poly_neg (poly_neg p) = p`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[poly_neg;poly_cmul];
  REWRITE_TAC[poly_neg;poly_cmul];
  REAL_SIMP_TAC;
  AP_TERM_TAC;
  ASM_MESON_TAC[poly_neg;poly_cmul];
]);;
(* }}} *)

let POLY_PNEG_NEG = prove_by_refinement(
 `!p n. poly_neg (pneg_aux (SUC n) p) = pneg_aux n p`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  ASM_REWRITE_TAC[pneg_aux;poly_neg;poly_cmul];
  REWRITE_TAC[pneg_aux];
  REPEAT STRIP_TAC;
  REWRITE_TAC[POLY_PNEG_AUX_SUC];
  REWRITE_TAC[poly_neg;poly_cmul];
  REAL_SIMP_TAC;
  AP_TERM_TAC;
  REWRITE_TAC[GSYM poly_neg];
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[GSYM POLY_NEG_NEG]));
  POP_ASSUM (ONCE_REWRITE_TAC o list);
  REWRITE_TAC[];
]);;
(* }}} *)

let POLY_PNEG_AUX = prove_by_refinement(
 `!k p n. EVEN n ==> (poly p (-- k) = poly (pneg_aux n p) k)`,
(* {{{ Proof *)
[
  STRIP_TAC;
  LIST_INDUCT_TAC;
  REPEAT STRIP_TAC;
  REWRITE_TAC[pneg_aux;poly];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> RULE_ASSUM_TAC (fun y -> MATCH_MP y x) THEN ASSUME_TAC x);
  REWRITE_TAC[poly;pneg_aux];
  REAL_SIMP_TAC;
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  CLAIM `-- &1 pow n = &1`;
  REWRITE_TAC[REAL_POW_NEG];
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  DISCH_THEN SUBST1_TAC;
  REAL_SIMP_TAC;
  AP_TERM_TAC;
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV[GSYM POLY_PNEG_NEG]));
  REWRITE_TAC[POLY_NEG];
  REAL_SIMP_TAC;
]);;
(* }}} *)

let POLY_PNEG = prove_by_refinement(
 `!p x. poly p (-- x) = poly (pneg p) x`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[pneg;poly];
  REWRITE_TAC[pneg;poly];
  REPEAT STRIP_TAC;
  CLAIM `poly (pneg_aux 0 (CONS h t)) x = poly (CONS h t) (--x)`;
  ASM_MESON_TAC[POLY_PNEG_AUX;EVEN];
  DISCH_THEN SUBST1_TAC;
  REWRITE_TAC[poly];
]);;
(* }}} *)

let DEGREE_0 = prove_by_refinement(
 `degree [] = 0 `,
(* {{{ Proof *)
[
  REWRITE_TAC[degree];
  REWRITE_TAC[normalize;LENGTH];
  ARITH_TAC;
]);;
(* }}} *)

let EVEN_ODD = prove_by_refinement(
 `!x. EVEN (SUC x) = ODD x`,
(* {{{ Proof *)
[
  REWRITE_TAC[EVEN;NOT_EVEN];
]);;
(* }}} *)

let ODD_EVEN = prove_by_refinement(
 `!x. ODD (SUC x) = EVEN x`,
(* {{{ Proof *)
[
  REWRITE_TAC[ODD;NOT_ODD];
]);;
(* }}} *)

let PNEG_CONS = prove_by_refinement(
 `!p. pneg (CONS h t) = CONS h (neg (pneg t))`,
(* {{{ Proof *)
[
  REWRITE_TAC[pneg;pneg_aux];
  REAL_SIMP_TAC;
  ONCE_REWRITE_TAC[GSYM POLY_PNEG_NEG];
  REWRITE_TAC[POLY_PNEG_AUX_SUC];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[pneg;pneg_aux;];
  REWRITE_ASSUMS !LIST_REWRITES;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[GSYM pneg];
]);;
(* }}} *)

let PNEG_NIL = prove_by_refinement(
 `!p. (pneg p = []) <=> (p = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN
  MESON_TAC[pneg;NOT_CONS_NIL;pneg_aux];
]);;
(* }}} *)

let PNEG_AUX_NIL = prove_by_refinement(
 `!p n. (pneg_aux n p = []) <=> (p = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN
  MESON_TAC[pneg;NOT_CONS_NIL;pneg_aux];
]);;
(* }}} *)

let POLY_CMUL_NIL = prove_by_refinement(
 `!p. (c ## p = []) <=> (p = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN
  MESON_TAC[poly_cmul;NOT_CONS_NIL;pneg_aux];
]);;
(* }}} *)

let POLY_NEG_NIL = prove_by_refinement(
 `!p. (poly_neg p = []) <=> (p = [])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN
  MESON_TAC[poly_neg;poly_cmul;NOT_CONS_NIL];
]);;
(* }}} *)

let NEG_LAST = prove_by_refinement(
 `!p. ~(p = []) ==> (LAST (neg p) = -- LAST p)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  DISCH_THEN IGNORE;
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[poly_neg;poly_cmul;LAST;];
  REAL_ARITH_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  ASM_SIMP_TAC[LAST_CONS;poly_neg;poly_cmul;];
  CLAIM `~(-- &1 ## t = [])`;
  ASM_MESON_TAC[POLY_CMUL_NIL];
  STRIP_TAC;
  ASM_SIMP_TAC[LAST_CONS];
  ASM_MESON_TAC[poly_neg;];
]);;
(* }}} *)

let POLY_PNEG_LAST = prove_by_refinement(
 `!p. normal p ==>
      (EVEN (degree p) ==> (LAST p = LAST (pneg p))) /\
      (ODD (degree p) ==> (LAST p = -- LAST (pneg p)))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[normal];
  STRIP_TAC;
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[LAST;pneg;pneg_aux];
  REAL_SIMP_TAC;
  ASM_MESON_TAC[DEGREE_SING;EVEN;NOT_EVEN];
  CLAIM `normal t`;
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_MESON_TAC[];
  DISCH_THEN (fun x -> RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x);
  STRIP_TAC;
  STRIP_TAC;
  CLAIM `ODD (degree t)`;
  MATCH_EQ_MP_TAC EVEN_ODD;
  ASM_MESON_TAC[DEGREE_CONS;ADD1;ADD_SYM];
  DISCH_THEN (fun x -> RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[LAST_CONS];
  REWRITE_TAC[PNEG_CONS];
  CLAIM `~(neg (pneg t) = [])`;
  ASM_MESON_TAC[POLY_NEG_NIL;PNEG_NIL];
  STRIP_TAC;
  ASM_SIMP_TAC[LAST_CONS];
  ASM_MESON_TAC[NEG_LAST;PNEG_NIL];
  CLAIM `normal t`;
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_MESON_TAC[];
  REPEAT STRIP_TAC;
  CLAIM `EVEN (degree t)`;
  MATCH_EQ_MP_TAC ODD_EVEN;
  ASM_MESON_TAC[DEGREE_CONS;ADD1;ADD_SYM];
  DISCH_THEN (fun x -> RULE_ASSUM_TAC (REWRITE_RULE [x]) THEN ASSUME_TAC x);
  ASM_SIMP_TAC[LAST_CONS];
  REWRITE_TAC[PNEG_CONS];
  CLAIM `~(neg (pneg t) = [])`;
  ASM_MESON_TAC[POLY_NEG_NIL;PNEG_NIL];
  STRIP_TAC;
  ASM_SIMP_TAC[LAST_CONS];
  ASM_SIMP_TAC[NEG_LAST;PNEG_NIL];
  REAL_SIMP_TAC;
]);;
(* }}} *)

let PNEG_AUX_LENGTH = prove_by_refinement(
 `!p n. LENGTH (pneg_aux n p) = LENGTH p`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH;pneg;pneg_aux;];
  REWRITE_TAC[LENGTH;pneg;pneg_aux;];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let PNEG_LENGTH = prove_by_refinement(
 `!p. LENGTH (pneg p) = LENGTH p`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH;pneg;pneg_aux;];
  REWRITE_TAC[LENGTH;pneg;pneg_aux;];
  ASM_MESON_TAC[PNEG_AUX_LENGTH];
]);;
(* }}} *)

let LAST_PNEG_AUX_0 = prove_by_refinement(
 `!p n. ~(p = []) ==> ((LAST p = &0) <=> (LAST (pneg_aux n p) = &0))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[];
  STRIP_TAC;
  DISCH_THEN IGNORE;
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[LAST;pneg;pneg_aux;];
  REAL_SIMP_TAC;
  ASM_SIMP_TAC[LAST_CONS;pneg;pneg_aux;];
  REAL_SIMP_TAC;
  EQ_TAC;
  DISCH_THEN SUBST1_TAC;
  REAL_SIMP_TAC;
  STRIP_TAC;
  MP_TAC (ISPECL[`-- &1`;`n:num`] POW_NZ);
  REAL_SIMP_TAC;
  REWRITE_TAC[ARITH_RULE `~(-- &1 = &0)`];
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ENTIRE];
  ASM_SIMP_TAC[LAST_CONS];
  REWRITE_TAC[pneg_aux];
  CLAIM `~(pneg_aux (SUC n) t = [])`;
  ASM_MESON_TAC[PNEG_AUX_NIL];
  STRIP_TAC;
  ASM_SIMP_TAC[LAST_CONS];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let LAST_PNEG_0 = prove_by_refinement(
 `!p n. ~(p = []) ==> ((LAST p = &0) = (LAST (pneg p) = &0))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC THEN MESON_TAC[LAST_PNEG_AUX_0;pneg];
]);;
(* }}} *)

let PNEG_LAST = prove_by_refinement(
  `!p. ~(p = []) ==> (LAST (pneg p) = LAST p) \/ (LAST (pneg p) = -- LAST p)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CASES_ON `normal p`;
  MP_TAC (ISPEC `p:real list` POLY_PNEG_LAST);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  DISJ_CASES_TAC (ISPEC `degree p` EVEN_OR_ODD);
  ASM_MESON_TAC[];
  ASM_MESON_TAC !REAL_REWRITES;
  REWRITE_ASSUMS[NORMAL_ID;DE_MORGAN_THM;];
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `LENGTH p = 0`;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  ASM_MESON_TAC[LENGTH_0];
  ASM_REWRITE_TAC[];
  DISJ1_TAC;
  ASM_MESON_TAC[LAST_PNEG_0];
]);;
(* }}} *)

let NORMAL_PNEG = prove_by_refinement(
 `!p. normal p = normal (pneg p)`,
(* {{{ Proof *)
[
  REWRITE_TAC[NORMAL_ID];
  REPEAT STRIP_TAC;
  EQ_TAC;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[PNEG_LENGTH];
  MP_TAC (ISPEC `p:real list` PNEG_LAST);
  CLAIM `~(p = [])`;
  ASM_MESON_TAC[LENGTH_NZ];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  REPEAT STRIP_TAC;
  ONCE_REWRITE_TAC[GSYM PNEG_LENGTH];
  ASM_REWRITE_TAC[];
  MP_TAC (ISPEC `p:real list` PNEG_LAST);
  CLAIM `~(p = [])`;
  ASM_MESON_TAC[LENGTH_NZ;PNEG_LENGTH];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let PNEG_AUX_NORMALIZE_LENGTH = prove_by_refinement(
 `!p n. LENGTH (normalize (pneg_aux n p)) = LENGTH (normalize p)`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[normalize;LENGTH;pneg_aux;];
  REWRITE_TAC[normalize;LENGTH;pneg;pneg_aux;];
  STRIP_TAC;
  REPEAT COND_CASES_TAC THEN TRY (ASM_SIMP_TAC !LIST_REWRITES);
  LABEL_ALL_TAC;
  KEEP ["Z-2";"Z-0"];
  CLAIM `~(-- &1 pow n = &0)`;
  MATCH_MP_TAC REAL_POW_NZ;
  REAL_ARITH_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ENTIRE];
  ASM_MESON_TAC[LENGTH_0];
  CLAIM `~(-- &1 pow n = &0)`;
  MATCH_MP_TAC REAL_POW_NZ;
  REAL_ARITH_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ENTIRE];
  ASM_MESON_TAC[LENGTH_0];
  ASM_MESON_TAC[LENGTH_0];
]);;

(* }}} *)

let PNEG_NORMALIZE_LENGTH = prove_by_refinement(
 `!p n. LENGTH (normalize (pneg p)) = LENGTH (normalize p)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[pneg];
  ASM_MESON_TAC[PNEG_AUX_NORMALIZE_LENGTH;pneg;pneg_aux;];
]);;
(* }}} *)

let DEGREE_PNEG = prove_by_refinement(
 `!p. degree (pneg p) = degree p`,
(* {{{ Proof *)
[
  REWRITE_TAC[degree];
  ASM_MESON_TAC[PNEG_NORMALIZE_LENGTH];
]);;
(* }}} *)

let PNEG_SING = prove_by_refinement(
 `!p. (pneg p = [x]) <=> (p = [x])`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[pneg;pneg_aux];
  EQ_TAC;
  REPEAT STRIP_TAC;
  LIST_SIMP_TAC;
  STRIP_TAC;
  REWRITE_ASSUMS[pneg;pneg_aux];
  POP_ASSUM MP_TAC;
  REAL_SIMP_TAC;
  LIST_SIMP_TAC;
  MESON_TAC[];
  POP_ASSUM MP_TAC;
  REWRITE_TAC[pneg;pneg_aux];
  LIST_SIMP_TAC;
  ASM_MESON_TAC[PNEG_AUX_NIL];
  REWRITE_TAC[pneg;pneg_aux];
  REAL_SIMP_TAC;
  LIST_SIMP_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[pneg_aux];
]);;
(* }}} *)

let PNEG_NONCONSTANT = prove_by_refinement(
 `!p. nonconstant (pneg p) = nonconstant p`,
(* {{{ Proof *)
[
  REWRITE_TAC[nonconstant];
  STRIP_TAC THEN EQ_TAC;
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[NORMAL_PNEG];
  POP_ASSUM (REWRITE_ASSUMS o list);
  REWRITE_ASSUMS[pneg;pneg_aux];
  POP_ASSUM MP_TAC;
  REAL_SIMP_TAC;
  MESON_TAC[];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[NORMAL_PNEG];
  ASM_MESON_TAC[PNEG_SING];
]);;
(* }}} *)

let LAST_UNBB_EVEN_NEG = prove_by_refinement(
 `!p. nonconstant p /\ EVEN (degree p) /\ LAST p < &0 ==>
       mono_unbounded_below (\n. poly p (-- &n))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[POLY_PNEG];
  MATCH_MP_TAC LAST_UNB_NEG;
  ASM_REWRITE_TAC[PNEG_NONCONSTANT];
  ASM_MESON_TAC[POLY_PNEG_LAST;nonconstant;];
]);;
(* }}} *)

let POLY_PNEG_LAST2 = prove_by_refinement(
  `!p. normal p
         ==> (EVEN (degree p) ==> (LAST (pneg p) = LAST p)) /\
             (ODD (degree p) ==> (LAST (pneg p) = -- LAST p))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[POLY_PNEG_LAST];
  ASM_MESON_TAC([POLY_PNEG_LAST; ARITH_RULE `(--x = y) <=> (x = -- y)` ]);
]);;
(* }}} *)

let LAST_UNB_ODD_NEG = prove_by_refinement(
 `!p. nonconstant p /\ ODD (degree p) /\ LAST p < &0 ==>
       mono_unbounded_above (\n. poly p (-- &n))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[POLY_PNEG];
  MATCH_MP_TAC LAST_UNB;
  ASM_REWRITE_TAC[PNEG_NONCONSTANT];
  CLAIM `LAST (pneg p) = -- LAST p`;
  ASM_MESON_TAC[POLY_PNEG_LAST2;nonconstant;];
  DISCH_THEN SUBST1_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let LAST_UNB_EVEN_POS = prove_by_refinement(
 `!p. nonconstant p /\ EVEN (degree p) /\ &0 < LAST p ==>
       mono_unbounded_above (\n. poly p (-- &n))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[POLY_PNEG];
  MATCH_MP_TAC LAST_UNB;
  ASM_REWRITE_TAC[PNEG_NONCONSTANT];
  ASM_MESON_TAC[POLY_PNEG_LAST2;nonconstant;];
]);;
(* }}} *)

let LAST_UNB_ODD_POS = prove_by_refinement(
 `!p. nonconstant p /\ ODD (degree p) /\ &0 < LAST p ==>
       mono_unbounded_below (\n. poly p (-- &n))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[POLY_PNEG];
  MATCH_MP_TAC LAST_UNB_NEG;
  ASM_REWRITE_TAC[PNEG_NONCONSTANT];
  CLAIM `LAST (pneg p) = -- LAST p`;
  ASM_MESON_TAC[POLY_PNEG_LAST2;nonconstant;];
  DISCH_THEN SUBST1_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let PNEG_NORMALIZE_LENGTH = prove_by_refinement(
 `!p n. LENGTH (normalize (pneg p)) = LENGTH (normalize p)`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[pneg];
  ASM_MESON_TAC[PNEG_AUX_NORMALIZE_LENGTH;pneg;pneg_aux;];
]);;
(* }}} *)

let POLY_DIFF_AUX_NORMAL = prove_by_refinement(
 `!p n. ~(n = 0) ==> (normal p = normal (poly_diff_aux n p))`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[normal;poly_diff_aux;];
  REPEAT STRIP_TAC;
  REWRITE_TAC[poly_diff_aux];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[poly_diff_aux;];
  REWRITE_TAC[normal];
  EQ_TAC;
  REPEAT STRIP_TAC;
  REWRITE_TAC[normalize];
  COND_CASES_TAC;
  CLAIM `~(h = &0)`;
  ASM_MESON_TAC[normal;normalize];
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_INJ];
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[NOT_CONS_NIL];
  STRIP_TAC;
  ASM_REWRITE_TAC[NOT_CONS_NIL];
  REWRITE_TAC[NORMALIZE_SING];
  CLAIM `~(&n * h = &0)`;
  ASM_MESON_TAC[normalize];
  ASM_MESON_TAC[REAL_ENTIRE;REAL_INJ;normalize];
  EQ_TAC;
  REPEAT STRIP_TAC;
  CLAIM `normal t`;
  ASM_MESON_TAC[NORMAL_TAIL];
  STRIP_TAC;
  MATCH_MP_TAC NORMAL_CONS;
  ASM_MESON_TAC[ARITH_RULE `~(SUC x = 0)`];
  STRIP_TAC;
  MATCH_MP_TAC NORMAL_CONS;
  MP_TAC (ARITH_RULE  `~(SUC n = 0)`);
  DISCH_THEN (fun x -> FIRST_ASSUM (fun y -> (MP_TAC (MATCH_MP y x))));
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC NORMAL_TAIL;
  EXISTS_TAC `&n * h`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[poly_diff_aux;NOT_CONS_NIL;list_CASES];
]);;

(* }}} *)

let POLY_DIFF_NORMAL = prove_by_refinement(
 `!p. nonconstant p ==> normal (poly_diff p)`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  ASM_MESON_TAC[normal;poly_diff;poly_diff_aux;POLY_DIFF_AUX_NORMAL;ARITH_RULE `~(1 = 0)`;nonconstant;];
  REWRITE_TAC[poly_diff;NOT_CONS_NIL;TL];
  REWRITE_TAC[nonconstant];
  STRIP_TAC;
  CLAIM `normal t`;
  MATCH_MP_TAC NORMAL_TAIL;
  EXISTS_TAC `h:real`;
  ASM_MESON_TAC[normal];
  STRIP_TAC;
  ASM_MESON_TAC[normal;poly_diff;poly_diff_aux;POLY_DIFF_AUX_NORMAL;ARITH_RULE `~(1 = 0)`];
]);;

(* }}} *)

let POLY_DIFF_AUX_NORMAL2 = prove_by_refinement(
 `!p n. ~(n = 0) ==> (normal (poly_diff_aux n p) <=> normal p)`,
(* {{{ Proof *)
[MESON_TAC[POLY_DIFF_AUX_NORMAL]]);;
(* }}} *)

let POLY_DIFF_AUX_DEGREE = prove_by_refinement(
 `!p m n. ~(n = 0) /\ ~(m = 0) /\ normal p ==>
    (degree (poly_diff_aux n p) = degree (poly_diff_aux m p))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[poly_diff_aux];
  REPEAT STRIP_TAC;
  REWRITE_TAC[poly_diff_aux];
  CASES_ON `t = []`;
  ASM_REWRITE_TAC[poly_diff_aux;DEGREE_SING];
  CLAIM `normal (poly_diff_aux (SUC n) t)`;
  ASM_SIMP_TAC[POLY_DIFF_AUX_NORMAL2;NOT_SUC];
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_REWRITE_TAC[];
  EXISTS_TAC `h:real`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `normal (poly_diff_aux (SUC m) t)`;
  ASM_SIMP_TAC[POLY_DIFF_AUX_NORMAL2;NOT_SUC];
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_REWRITE_TAC[];
  EXISTS_TAC `h:real`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  ASM_SIMP_TAC[DEGREE_CONS];
  AP_TERM_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  STRIP_TAC;
  ARITH_TAC;
  STRIP_TAC;
  ARITH_TAC;
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_MESON_TAC[];
]);;
(* }}} *)

let poly_diff_aux_odd = prove_by_refinement(
 `!p n. nonconstant p ==>
  (EVEN (degree p) = EVEN (degree (poly_diff_aux n p))) /\
  (ODD (degree p) = ODD (degree (poly_diff_aux n p)))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[normal;nonconstant;];
  STRIP_TAC;
  DISCH_THEN (fun x -> ASSUME_TAC x THEN MP_TAC x);
  REWRITE_TAC[nonconstant];
  STRIP_TAC;
  CASES_ON `t = []`;
  ASM_MESON_TAC[nonconstant;normal];
  REWRITE_TAC[poly_diff_aux];
  CLAIM `normal t`;
  ASM_MESON_TAC[NORMAL_TAIL];
  STRIP_TAC;
  CLAIM `normal (poly_diff_aux (SUC n) t)`;
  ASM_MESON_TAC[nonconstant;normal;POLY_DIFF_AUX_NORMAL;NOT_SUC];
  STRIP_TAC;
  CASES_ON `?x. t = [x]`;
  POP_ASSUM MP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
  CLAIM `~(x = &0)`;
  ASM_MESON_TAC[normal;normalize];
  STRIP_TAC;
  CLAIM `degree [h; x] = 1`;
  CLAIM `normalize [h; x] = [h; x]`;
  ASM_MESON_TAC[normal];
  DISCH_THEN SUBST1_TAC;
  CLAIM `LENGTH [h; x] = 2`;
  ASM_MESON_TAC[LENGTH_PAIR];
  STRIP_TAC;
  REWRITE_TAC[degree];
  CLAIM `normal [h; x]`;
  ASM_MESON_TAC[normal;normalize];
  DISCH_THEN (fun x -> ASSUME_TAC x THEN MP_TAC x);
  REWRITE_TAC[normal];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  ARITH_TAC;
  STRIP_TAC;
  ASM_REWRITE_TAC[poly_diff_aux;];
  CLAIM `~(&(SUC n) * x = &0)`;
  ASM_MESON_TAC[normal;normalize;REAL_ENTIRE;ARITH_RULE `~(SUC n = 0)`;REAL_INJ];
  STRIP_TAC;
  CLAIM `degree [&n * h; &(SUC n) * x] = 1`;
  REWRITE_TAC[degree];
  ASM_REWRITE_TAC[normalize;NOT_CONS_NIL;LENGTH;];
  ARITH_TAC;
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[DEGREE_CONS];
  CLAIM `nonconstant t`;
  ASM_MESON_TAC[nonconstant];
  STRIP_TAC;
  ONCE_REWRITE_TAC[ADD_SYM];
  REWRITE_TAC[GSYM ADD1];
  ASM_SIMP_TAC[EVEN;ODD];
  ASM_MESON_TAC[POLY_DIFF_AUX_DEGREE];
]);;
(* }}} *)

let poly_diff_parity = prove_by_refinement(
 `!p n. nonconstant p ==>
  (EVEN (degree p) = ODD (degree (poly_diff p))) /\
  (ODD (degree p) = EVEN (degree (poly_diff p)))`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[nonconstant;normal];
  STRIP_TAC;
  DISCH_ASS;
  REWRITE_TAC[nonconstant];
  STRIP_TAC;
  REWRITE_TAC[poly_diff];
  LIST_SIMP_TAC;
  CLAIM `~(1 = 0)`;
  ARITH_TAC;
  STRIP_TAC;
  CLAIM `normal t`;
  MATCH_MP_TAC NORMAL_TAIL;
  ASM_MESON_TAC[nonconstant;normal];
  STRIP_TAC;
  ASM_SIMP_TAC[DEGREE_CONS];
  CASES_ON `?x. t = [x]`;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `~(x = &0)`;
  ASM_MESON_TAC[normal;normalize];
  STRIP_TAC;
  ASM_REWRITE_TAC[poly_diff_aux;DEGREE_SING;degree;normalize;LENGTH;NOT_CONS_NIL;];
  CLAIM `~(&1 * x = &0)`;
  ASM_MESON_TAC[REAL_ENTIRE;ARITH_RULE `~(&1 = &0)`];
  STRIP_TAC;
  ASM_REWRITE_TAC[LENGTH];
  REWRITE_TAC[ARITH_RULE `1 + x = SUC x`];
  ASM_MESON_TAC[EVEN;ODD;NOT_EVEN;NOT_ODD;];
  CLAIM `nonconstant t`;
  ASM_MESON_TAC[nonconstant];
  DISCH_ASS;
  DISCH_THEN (fun x -> REWRITE_ASSUMS[x] THEN ASSUME_TAC x);
  ONCE_REWRITE_TAC[ADD_SYM];
  REWRITE_TAC[GSYM ADD1;EVEN;ODD];
  CLAIM `?h' t'. t = CONS h' t'`;
  ASM_MESON_TAC[nonconstant;normal;list_CASES];
  STRIP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS [x] THEN REWRITE_TAC[x] THEN ASSUME_TAC x);
  REWRITE_ASSUMS[poly_diff;NOT_CONS_NIL;TL];
  REWRITE_TAC[poly_diff_aux];
  CLAIM `normal t'`;
  ASM_MESON_TAC[nonconstant;NORMAL_TAIL;normal];
  STRIP_TAC;
  CLAIM `normal (poly_diff_aux (SUC 1) t')`;
  ASM_MESON_TAC[POLY_DIFF_AUX_NORMAL2;NOT_SUC];
  STRIP_TAC;
  ASM_SIMP_TAC[DEGREE_CONS];
  ONCE_REWRITE_TAC[ADD_SYM];
  REWRITE_TAC[GSYM ADD1;EVEN;ODD];
  CLAIM `normal (poly_diff_aux 1 t')`;
  ASM_MESON_TAC[POLY_DIFF_AUX_NORMAL2;ONE;NOT_SUC];
  STRIP_TAC;
  ASM_MESON_TAC[POLY_DIFF_AUX_DEGREE;ONE;NOT_SUC];
]);;
(* }}} *)

let poly_diff_parity2 = prove_by_refinement(
 `!p n. nonconstant p ==>
  (ODD (degree (poly_diff p)) = EVEN (degree p)) /\
  (EVEN (degree (poly_diff p)) = ODD (degree p))`,
(* {{{ Proof *)
[MESON_TAC[poly_diff_parity]]);;
(* }}} *)

let normal_nonconstant = prove_by_refinement(
 `!p. normal p /\ 0 < degree p ==> nonconstant p`,
(* {{{ Proof *)
[
  REWRITE_TAC[nonconstant];
  ASM_MESON_TAC[DEGREE_SING;LT_REFL];
]);;
(* }}} *)

let nmax_le = prove_by_refinement(
 `!n m. n <= nmax n m /\ m <= nmax n m`,
(* {{{ Proof *)
[
  REWRITE_TAC[nmax];
  REPEAT STRIP_TAC;
  COND_CASES_TAC;
  ARITH_TAC;
  ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_UP_LEFT = prove_by_refinement(
 `!p. nonconstant p /\ (?X. !x. x < X ==> poly (poly_diff p) x < &0) ==>
   (?Y. !y. y < Y ==> &0 < poly p y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `mono_unbounded_above (\n. poly p (-- &n))`;
  REWRITE_TAC[POLY_PNEG];
  DISJ_CASES_TAC (ISPEC `degree p` EVEN_OR_ODD);
  MATCH_MP_TAC mua_quotient_limit;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. LAST (pneg p) * &n pow degree (pneg p))`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  BETA_TAC;
  MATCH_MP_TAC LIM_POLY2;
  MATCH_EQ_MP_TAC NORMAL_PNEG;
  ASM_MESON_TAC[nonconstant];
  MATCH_MP_TAC POW_UNB_CON;
  STRIP_TAC;
  REWRITE_TAC[DEGREE_PNEG];
  REWRITE_TAC[degree];
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[nonconstant;normal];
  DISCH_THEN SUBST1_TAC;
  CLAIM `~(LENGTH p = 0)`;
  ASM_MESON_TAC[nonconstant;normal;LENGTH_NZ;LENGTH_0;degree];
  STRIP_TAC;
  CLAIM `~(LENGTH p = 1)`;
  ASM_MESON_TAC[nonconstant;normal;LENGTH_NZ;LENGTH_1;degree];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  (* save *)
  CLAIM `LAST (pneg p) = LAST p`;
  ASM_MESON_TAC[GSYM POLY_PNEG_LAST;nonconstant;];
  DISCH_THEN SUBST1_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `x < y <=> ~(x = y) /\ ~(y < x)`];
  STRIP_TAC;
  ASM_MESON_TAC[NORMAL_ID;nonconstant];
  STRIP_TAC;
  CLAIM `ODD (degree (poly_diff p))`;
  ASM_SIMP_TAC[poly_diff_parity2];
  STRIP_TAC;
  CLAIM `nonconstant (poly_diff p)`;
  MATCH_MP_TAC normal_nonconstant;
  STRIP_TAC;
  MATCH_MP_TAC NONCONSTANT_DIFF_NORMAL;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `mono_unbounded_above (\n. poly (poly_diff p) (-- &n))`;
  MATCH_MP_TAC LAST_UNB_ODD_NEG;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[POLY_DIFF_LAST_LT];
  REWRITE_TAC[mono_unbounded_above];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  (* save *)
  MP_TAC (ISPEC `-- (X - &1)` REAL_ARCH_SIMPLE);
  DISCH_THEN (X_CHOOSE_TAC `M:num`);
  CLAIM `-- &M <= X - &1`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-2" (MP_TAC o ISPEC `nmax M N`);
  STRIP_TAC;
  CLAIM `N <= nmax M N`;
  REWRITE_TAC[nmax_le];
  DISCH_THEN (REWRITE_ASSUMS o list);
  CLAIM `-- &(nmax M N) < X`;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `-- &M`;
  STRIP_TAC;
  REWRITE_TAC[nmax];
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN ARITH_TAC;
  USE_THEN "Z-0" MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[ARITH_RULE `~(x < &0 /\ &0 < x)`];
  (* save *)
  REWRITE_TAC[GSYM POLY_PNEG];
  MATCH_MP_TAC LAST_UNB_ODD_NEG;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[GSYM POLY_DIFF_LAST_LT];
  CASES_ON `?x. poly_diff p = [x]`;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[LAST];
  LABEL_ALL_TAC;
  USE_THEN "Z-2" MP_TAC;
  POP_ASSUM (fun x -> REWRITE_TAC[x] THEN ASSUME_TAC x);
  REWRITE_TAC[poly];
  REAL_SIMP_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  EXISTS_TAC `X - &1`;
  REAL_ARITH_TAC;
  CLAIM `nonconstant (poly_diff p)`;
  REWRITE_TAC[nonconstant];
  STRIP_TAC;
  MATCH_MP_TAC POLY_DIFF_NORMAL;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `EVEN (degree (poly_diff p))`;
  ASM_MESON_TAC[poly_diff_parity];
  STRIP_TAC;
  ONCE_REWRITE_TAC[ARITH_RULE `x < y <=> ~(y < x) /\ ~(y = x)`];
  REPEAT STRIP_TAC;
  CLAIM `mono_unbounded_above (\n. poly (poly_diff p) (-- (&n)))`;
  MATCH_MP_TAC LAST_UNB_EVEN_POS;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[mono_unbounded_above];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  (* save *)
  MP_TAC (ISPEC `-- (X - &1)` REAL_ARCH_SIMPLE);
  DISCH_THEN (X_CHOOSE_TAC `M:num`);
  CLAIM `-- &M <= X - &1`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-2" (MP_TAC o ISPEC `nmax M N`);
  STRIP_TAC;
  CLAIM `N <= nmax M N`;
  REWRITE_TAC[nmax_le];
  DISCH_THEN (REWRITE_ASSUMS o list);
  CLAIM `-- &(nmax M N) < X`;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `-- &M`;
  STRIP_TAC;
  REWRITE_TAC[nmax];
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN ARITH_TAC;
  USE_THEN "Z-0" MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[ARITH_RULE `~(x < &0 /\ &0 < x)`];
  ASM_MESON_TAC[nonconstant;NORMAL_ID];
  (* save xxx *)
  REWRITE_TAC[mono_unbounded_above];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  MP_TAC (ISPEC `-- (X - &1)` REAL_ARCH_SIMPLE);
  DISCH_THEN (X_CHOOSE_TAC `M:num`);
  ABBREV_TAC `k = nmax N M`;
  EXISTS_TAC `-- &k`;
  REPEAT STRIP_TAC;
  REWRITE_TAC [ARITH_RULE `x < y <=> ~(y <= x)`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`y:real`;`-- &k`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  CLAIM `&0 < (-- &k) - y`;
  USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `poly (poly_diff p) x < &0`;
  FIRST_ASSUM MATCH_MP_TAC;
  MATCH_MP_TAC REAL_LTE_TRANS;
  EXISTS_TAC `-- &k`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LE_TRANS;
  EXISTS_TAC `-- &M`;
  STRIP_TAC;
  USE_THEN "Z-5" (SUBST1_TAC o GSYM);
  REWRITE_TAC[nmax];
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN ARITH_TAC;
  USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  (* save *)
  CLAIM `N <= k:num`;
  USE_THEN "Z-5" (SUBST1_TAC o GSYM);
  REWRITE_TAC[nmax] THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < poly p (-- &k)`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `&0 < poly p (-- &k) - poly p y`;
  LABEL_ALL_TAC;
  USE_ASSUM_LIST ["Z-10";"Z-3"] MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(-- &k - y) * poly (poly_diff p) x < &0`;
  REWRITE_TAC[REAL_MUL_LT];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC;
  USE_THEN "Z-0" MP_TAC;
  REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_DOWN_LEFT = prove_by_refinement(
 `!p. nonconstant p /\ (?X. !x. x < X ==> &0 < poly (poly_diff p) x) ==>
   (?Y. !y. y < Y ==> poly p y < &0)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  CLAIM `mono_unbounded_below (\n. poly p (-- &n))`;
  REWRITE_TAC[POLY_PNEG];
  DISJ_CASES_TAC (ISPEC `degree p` EVEN_OR_ODD);
  MATCH_MP_TAC mua_quotient_limit_neg;
  EXISTS_TAC `&1`;
  EXISTS_TAC `(\n. LAST (pneg p) * &n pow degree (pneg p))`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  BETA_TAC;
  MATCH_MP_TAC LIM_POLY2;
  MATCH_EQ_MP_TAC NORMAL_PNEG;
  ASM_MESON_TAC[nonconstant];
  MATCH_MP_TAC POW_UNBB_CON;
  STRIP_TAC;
  REWRITE_TAC[DEGREE_PNEG];
  REWRITE_TAC[degree];
  CLAIM `normalize p = p`;
  ASM_MESON_TAC[nonconstant;normal];
  DISCH_THEN SUBST1_TAC;
  CLAIM `~(LENGTH p = 0)`;
  ASM_MESON_TAC[nonconstant;normal;LENGTH_NZ;LENGTH_0;degree];
  STRIP_TAC;
  CLAIM `~(LENGTH p = 1)`;
  ASM_MESON_TAC[nonconstant;normal;LENGTH_NZ;LENGTH_1;degree];
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  (* save *)
  CLAIM `LAST (pneg p) = LAST p`;
  ASM_MESON_TAC[GSYM POLY_PNEG_LAST;nonconstant;];
  DISCH_THEN SUBST1_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `x < y <=> ~(x = y) /\ ~(y < x)`];
  STRIP_TAC;
  ASM_MESON_TAC[NORMAL_ID;nonconstant];
  STRIP_TAC;
  CLAIM `ODD (degree (poly_diff p))`;
  ASM_SIMP_TAC[poly_diff_parity2];
  STRIP_TAC;
  CLAIM `nonconstant (poly_diff p)`;
  MATCH_MP_TAC normal_nonconstant;
  STRIP_TAC;
  MATCH_MP_TAC NONCONSTANT_DIFF_NORMAL;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  POP_ASSUM MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `mono_unbounded_below (\n. poly (poly_diff p) (-- &n))`;
  MATCH_MP_TAC LAST_UNB_ODD_POS;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[POLY_DIFF_LAST_GT];
  REWRITE_TAC[mono_unbounded_below];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  (* save *)
  MP_TAC (ISPEC `-- (X - &1)` REAL_ARCH_SIMPLE);
  DISCH_THEN (X_CHOOSE_TAC `M:num`);
  CLAIM `-- &M <= X - &1`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-2" (MP_TAC o ISPEC `nmax M N`);
  STRIP_TAC;
  CLAIM `N <= nmax M N`;
  REWRITE_TAC[nmax_le];
  DISCH_THEN (REWRITE_ASSUMS o list);
  CLAIM `-- &(nmax M N) < X`;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `-- &M`;
  STRIP_TAC;
  REWRITE_TAC[nmax];
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN ARITH_TAC;
  USE_THEN "Z-0" MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[ARITH_RULE `~(x < &0 /\ &0 < x)`];
  (* save *)
  REWRITE_TAC[GSYM POLY_PNEG];
  MATCH_MP_TAC LAST_UNB_ODD_POS;
  ASM_REWRITE_TAC[];
  ASM_SIMP_TAC[GSYM POLY_DIFF_LAST_GT];
  CASES_ON `?x. poly_diff p = [x]`;
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  ASM_REWRITE_TAC[LAST];
  LABEL_ALL_TAC;
  USE_THEN "Z-2" MP_TAC;
  POP_ASSUM (fun x -> REWRITE_TAC[x] THEN ASSUME_TAC x);
  REWRITE_TAC[poly];
  REAL_SIMP_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  EXISTS_TAC `X - &1`;
  REAL_ARITH_TAC;
  CLAIM `nonconstant (poly_diff p)`;
  REWRITE_TAC[nonconstant];
  STRIP_TAC;
  MATCH_MP_TAC POLY_DIFF_NORMAL;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `EVEN (degree (poly_diff p))`;
  ASM_MESON_TAC[poly_diff_parity];
  STRIP_TAC;
  ONCE_REWRITE_TAC[ARITH_RULE `x < y <=> ~(y < x) /\ ~(y = x)`];
  REPEAT STRIP_TAC;
  CLAIM `mono_unbounded_below (\n. poly (poly_diff p) (-- (&n)))`;
  MATCH_MP_TAC LAST_UNBB_EVEN_NEG;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[mono_unbounded_below];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  (* save *)
  MP_TAC (ISPEC `-- (X - &1)` REAL_ARCH_SIMPLE);
  DISCH_THEN (X_CHOOSE_TAC `M:num`);
  CLAIM `-- &M <= X - &1`;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-2" (MP_TAC o ISPEC `nmax M N`);
  STRIP_TAC;
  CLAIM `N <= nmax M N`;
  REWRITE_TAC[nmax_le];
  DISCH_THEN (REWRITE_ASSUMS o list);
  CLAIM `-- &(nmax M N) < X`;
  MATCH_MP_TAC REAL_LET_TRANS;
  EXISTS_TAC `-- &M`;
  STRIP_TAC;
  REWRITE_TAC[nmax];
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN ARITH_TAC;
  USE_THEN "Z-0" MP_TAC THEN ARITH_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[ARITH_RULE `~(x < &0 /\ &0 < x)`];
  ASM_MESON_TAC[nonconstant;NORMAL_ID];
  (* save *)
  REWRITE_TAC[mono_unbounded_below];
  DISCH_THEN (MP_TAC o ISPEC `&0`);
  STRIP_TAC;
  MP_TAC (ISPEC `-- (X - &1)` REAL_ARCH_SIMPLE);
  DISCH_THEN (X_CHOOSE_TAC `M:num`);
  ABBREV_TAC `k = nmax N M`;
  EXISTS_TAC `-- &k`;
  REPEAT STRIP_TAC;
  REWRITE_TAC [ARITH_RULE `x < y <=> ~(y <= x)`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`y:real`;`-- &k`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  LABEL_ALL_TAC;
  CLAIM `&0 < (-- &k) - y`;
  USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < poly (poly_diff p) x`;
  FIRST_ASSUM MATCH_MP_TAC;
  MATCH_MP_TAC REAL_LTE_TRANS;
  EXISTS_TAC `-- &k`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LE_TRANS;
  EXISTS_TAC `-- &M`;
  STRIP_TAC;
  USE_THEN "Z-5" (SUBST1_TAC o GSYM);
  REWRITE_TAC[nmax];
  REWRITE_TAC[REAL_LE_NEG2; REAL_OF_NUM_LE] THEN ARITH_TAC;
  USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  (* save *)
  CLAIM `N <= k:num`;
  USE_THEN "Z-5" (SUBST1_TAC o GSYM);
  REWRITE_TAC[nmax] THEN ARITH_TAC;
  STRIP_TAC;
  CLAIM `poly p (-- &k) < &0`;
  ASM_MESON_TAC[];
  STRIP_TAC;
  CLAIM `poly p (-- &k) - poly p y < &0`;
  LABEL_ALL_TAC;
  USE_ASSUM_LIST ["Z-10";"Z-3"] MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (-- &k - y) * poly (poly_diff p) x`;
  REWRITE_TAC[REAL_MUL_GT];
  ASM_REWRITE_TAC[];
  POP_ASSUM MP_TAC;
  USE_THEN "Z-0" MP_TAC;
  REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_DOWN_LEFT2 = prove_by_refinement(
 `!p X. nonconstant p /\ (!x. x < X ==> &0 < poly (poly_diff p) x) ==>
   (?Y. Y < X /\ (!y. y < Y ==> poly p y < &0))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPEC `p:real list` POLY_DIFF_DOWN_LEFT);
  ASM_REWRITE_TAC[];
  ANTS_TAC;
  ASM_MESON_TAC[];
  STRIP_TAC;
  EXISTS_TAC `min X Y - &1`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_UP_LEFT2 = prove_by_refinement(
 `!p X. nonconstant p /\ (!x. x < X ==> poly (poly_diff p) x < &0) ==>
   (?Y. Y < X /\ (!y. y < Y ==> &0 < poly p y))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPEC `p:real list` POLY_DIFF_UP_LEFT);
  ASM_REWRITE_TAC[];
  ANTS_TAC;
  ASM_MESON_TAC[];
  STRIP_TAC;
  EXISTS_TAC `min X Y - &1`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_DOWN_LEFT3 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
   (!x. x < X ==> &0 < poly p' x) ==>
     (?Y. Y < X /\ (!y. y < Y ==> poly p y < &0))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPEC `p:real list` POLY_DIFF_DOWN_LEFT);
  ASM_REWRITE_TAC[];
  ANTS_TAC;
  ASM_MESON_TAC[];
  STRIP_TAC;
  EXISTS_TAC `min X Y - &1`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_UP_LEFT3 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
   (!x. x < X ==> poly p' x < &0) ==>
     (?Y. Y < X /\ (!y. y < Y ==> &0 < poly p y))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPEC `p:real list` POLY_DIFF_UP_LEFT);
  ASM_REWRITE_TAC[];
  ANTS_TAC;
  ASM_MESON_TAC[];
  STRIP_TAC;
  EXISTS_TAC `min X Y - &1`;
  REPEAT STRIP_TAC;
  REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_DOWN_LEFT4 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
   (!x. x < X ==> &0 < poly p' x) ==>
     (?Y. Y < X /\ (!y. y <= Y ==> poly p y < &0))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL[ `p:real list`;`p':real list`;`X:real`] POLY_DIFF_DOWN_LEFT3);
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  EXISTS_TAC `Y - &1`;
  STRIP_TAC;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_UP_LEFT4 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
   (!x. x < X ==> poly p' x < &0) ==>
     (?Y. Y < X /\ (!y. y <= Y ==> &0 < poly p y))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL[ `p:real list`;`p':real list`;`X:real`] POLY_DIFF_UP_LEFT3);
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  EXISTS_TAC `Y - &1`;
  STRIP_TAC;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_DOWN_LEFT5 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
   (!x. x < X ==> poly p' x > &0) ==>
     (?Y. Y < X /\ (!y. y <= Y ==> poly p y < &0))`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt];
  ASM_MESON_TAC[POLY_DIFF_DOWN_LEFT4];
]);;
(* }}} *)

let POLY_DIFF_UP_LEFT5 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
   (!x. x < X ==> poly p' x < &0) ==>
     (?Y. Y < X /\ (!y. y <= Y ==> poly p y > &0))`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt];
  MESON_TAC[POLY_DIFF_UP_LEFT4];
]);;
(* }}} *)

let NORMAL_PDIFF_LEM = prove_by_refinement(
 `!p. normal (poly_diff p) ==> nonconstant p`,
(* {{{ Proof *)
[
  LIST_INDUCT_TAC;
  REWRITE_TAC[normal;poly_diff;poly_diff_aux];
  REWRITE_TAC[nonconstant];
  REWRITE_TAC[poly_diff;poly_diff_aux;NOT_CONS_NIL;TL;];
  REPEAT STRIP_TAC;
  MATCH_MP_TAC NORMAL_CONS;
  ASM_MESON_TAC[POLY_DIFF_AUX_NORMAL;ARITH_RULE `~(1 = 0)`];
  CLAIM `t = []`;
  ASM_MESON_TAC !LIST_REWRITES;
  DISCH_THEN (REWRITE_ASSUMS o list);
  ASM_MESON_TAC[normal;poly_diff_aux];
]);;
(* }}} *)

let NORMAL_PDIFF = prove_by_refinement(
 `!p. nonconstant p = normal (poly_diff p)`,
(* {{{ Proof *)
[
  MESON_TAC[NORMAL_PDIFF_LEM;POLY_DIFF_NORMAL];
]);;
(* }}} *)

let POLY_DIFF_UP_RIGHT2 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. X < x ==> &0 < poly p' x) ==>
     (?Y. X < Y /\ (!y. Y <= y ==> &0 < poly p y))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL[ `p:real list`] (GEN_ALL POLY_DIFF_UP_RIGHT));
  ASM_REWRITE_TAC[];
  ANTS_TAC;
  ASM_MESON_TAC[];
  REPEAT STRIP_TAC;
  EXISTS_TAC `(max X Y) + &1`;
  STRIP_TAC;
  REAL_ARITH_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_DOWN_RIGHT2 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. X < x ==> poly p' x < &0) ==>
     (?Y. X < Y /\ (!y. Y <= y ==> poly p y < &0))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL[ `p:real list`] (GEN_ALL POLY_DIFF_DOWN_RIGHT));
  ASM_REWRITE_TAC[];
  ANTS_TAC;
  ASM_MESON_TAC[];
  REPEAT STRIP_TAC;
  EXISTS_TAC `(max X Y) + &1`;
  STRIP_TAC;
  REAL_ARITH_TAC;
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let POLY_DIFF_UP_RIGHT3 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. X < x ==> poly p' x > &0) ==>
     (?Y. X < Y /\ (!y. Y <= y ==> poly p y > &0))`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt;real_ge];
  MESON_TAC[POLY_DIFF_UP_RIGHT2];
]);;
(* }}} *)

let POLY_DIFF_DOWN_RIGHT3 = prove_by_refinement(
 `!p p' X. nonconstant p ==> (poly_diff p = p') ==>
     (!x. X < x ==> poly p' x < &0) ==>
     (?Y. X < Y /\ (!y. Y <= y ==> poly p y < &0))`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt;real_ge];
  MESON_TAC[POLY_DIFF_DOWN_RIGHT2];
]);;
(* }}} *)



