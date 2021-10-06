let inferisign_lem00 = prove_by_refinement(
  `x1 < x3 ==> x3 < x2 ==> (!x. x1 < x /\ x < x2 ==> P x) ==>
    (!x. x1 < x /\ x < x3 ==> P x) /\
    (!x. (x = x3) ==> P x) /\
    (!x. x3 < x /\ x < x2 ==> P x)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x3`;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x3`;
  ASM_REWRITE_TAC[];
]);;

(* }}} *)

let neg_neg_neq_thm = prove_by_refinement(
  `!x y p. x < y /\ poly p x < &0 /\ poly p y < &0 /\
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            (!z. x < z /\ z < y ==> poly p z < &0)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[ARITH_RULE `x < y <=> ~(y <= x)`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `&0 < poly p z - poly p x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-8" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (z - x) * poly (poly_diff p) x'`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p y - poly p z < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-13" MP_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(y - z) * poly (poly_diff p) x'' < &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REAL_ARITH_TAC;
  CLAIM `x' < x''`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`x':real`;`x'':real`] (REWRITE_RULE[real_gt] POLY_IVT_NEG));
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `x < x''' /\  x''' < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x'`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x''`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let neg_neg_neq_thm2 = prove_by_refinement(
  `!x y p. x < y ==> poly p x < &0 ==> poly p y < &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            (!z. x < z /\ z < y ==> poly p z < &0)`,
(* {{{ Proof *)
[
  REPEAT_N 7 STRIP_TAC;
  MATCH_MP_TAC neg_neg_neq_thm;
  ASM_MESON_TAC[];
]);;
(* }}} *)

let pos_pos_neq_thm = prove_by_refinement(
  `!x y p. x < y /\ &0 < poly p x /\ &0 < poly p y /\
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            (!z. x < z /\ z < y ==> &0 < poly p z)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[ARITH_RULE `x < y <=> ~(y <= x)`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p z - poly p x < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-8" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) x' < &0`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `&0 < poly p y - poly p z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-13" MP_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (y - z) * poly (poly_diff p) x''`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REAL_ARITH_TAC;
  CLAIM `x' < x''`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`x':real`;`x'':real`] (REWRITE_RULE[real_gt] POLY_IVT_POS));
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `x < x''' /\  x''' < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x'`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x''`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
]);;
(* }}} *)

let pos_pos_neq_thm2 = prove_by_refinement(
  `!x y p. x < y ==> poly p x > &0 ==> poly p y > &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            (!z. x < z /\ z < y ==> poly p z > &0)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt];
  REPEAT_N 7 STRIP_TAC;
  MATCH_MP_TAC pos_pos_neq_thm;
  ASM_MESON_TAC[];
]);;
(* }}} *)

let pos_neg_neq_thm = prove_by_refinement(
  `!x y p. x < y /\ &0 < poly p x /\ poly p y < &0 /\
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            ?X. x < X /\ X < y /\ (poly p X = &0) /\
              (!z. x < z /\ z < X ==> &0 < poly p z) /\
              (!z. X < z /\ z < y ==> poly p z < &0)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`y:real`] POLY_IVT_NEG);
  REWRITE_TAC[real_gt];
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `X:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  REPEAT STRIP_TAC;
  (* save *)
  ONCE_REWRITE_TAC[ARITH_RULE `x < y <=> ~(y < x \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `N:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `poly p z - poly p x < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-11" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) N < &0`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`X:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `&0 < &0 - poly p z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < X - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (X - z) * poly (poly_diff p) M`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  CLAIM `N < M`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`N:real`;`M:real`] (REWRITE_RULE[real_gt] POLY_IVT_POS));
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `K:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  (* save *)
  CLAIM `x < K /\  K < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `N`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `M`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  POP_ASSUM (ASSUME_TAC o GSYM);
  MP_TAC (ISPECL [`p:real list`;`z:real`;`X:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `(x:real = y) <=> (y = x)`];
  ASM_REWRITE_TAC[REAL_ENTIRE];
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  LABEL_ALL_TAC;
  POP_ASSUM MP_TAC;
  USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `x < M /\  M < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  REPEAT STRIP_TAC;
  ONCE_REWRITE_TAC[ARITH_RULE `x < y <=> ~(y < x \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`X:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `N:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM MP_TAC;
  REAL_SIMP_TAC;
  STRIP_TAC;
  CLAIM `&0 < (z - X) * poly (poly_diff p) N`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - X`;
  LABEL_ALL_TAC;
  USE_THEN "Z-7" MP_TAC THEN REAL_ARITH_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  LABEL_ALL_TAC;
  USE_THEN "Z-6" (REWRITE_TAC o list);
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `poly p y - poly p z < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-12" MP_TAC;
  USE_THEN "Z-5" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(y - z) * poly (poly_diff p) M < &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  CLAIM `N < M`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`N:real`;`M:real`] (REWRITE_RULE[real_gt] POLY_IVT_NEG));
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `K:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  (* save *)
  CLAIM `x < K /\  K < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `N`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `M`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`X:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `(x:real = y) <=> (y = x)`];
  ASM_REWRITE_TAC[REAL_ENTIRE];
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  LABEL_ALL_TAC;
  POP_ASSUM MP_TAC;
  USE_THEN "Z-5" MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `x < M /\  M < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
]);;

(* }}} *)


let pos_neg_neq_thm2 = prove_by_refinement(
  `!x y p. x < y ==> poly p x > &0 ==> poly p y < &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            ?X. x < X /\ X < y /\
              (!z. (z = X) ==> (poly p z = &0)) /\
              (!z. x < z /\ z < X ==> poly p z > &0) /\
              (!z. X < z /\ z < y ==> poly p z < &0)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL[`x:real`;`y:real`;`p:real list`] pos_neg_neq_thm);
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  EXISTS_TAC `X`;
  ASM_MESON_TAC[];
]);;
(* }}} *)

let neg_pos_neq_thm = prove_by_refinement(
  `!x y p. x < y /\ poly p x < &0 /\ &0 < poly p y /\
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            ?X. x < X /\ X < y /\ (poly p X = &0) /\
              (!z. x < z /\ z < X ==> poly p z < &0) /\
              (!z. X < z /\ z < y ==> &0 < poly p z)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`y:real`] POLY_IVT_POS);
  REWRITE_TAC[real_gt];
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `X:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  REPEAT STRIP_TAC;
  (* save *)
  ONCE_REWRITE_TAC[ARITH_RULE `x < y <=> ~(y < x \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `N:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `&0 < poly p z - poly p x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-11" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (z - x) * poly (poly_diff p) N`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`X:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `&0 - poly p z < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < X - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(X - z) * poly (poly_diff p) M < &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  CLAIM `N < M`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`N:real`;`M:real`] (REWRITE_RULE[real_gt] POLY_IVT_NEG));
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `K:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  (* save *)
  CLAIM `x < K /\  K < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `N`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `M`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`X:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `(x:real = y) <=> (y = x)`];
  ASM_REWRITE_TAC[REAL_ENTIRE];
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  LABEL_ALL_TAC;
  POP_ASSUM MP_TAC;
  USE_THEN "Z-4" MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `x < M /\  M < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  REPEAT STRIP_TAC;
  ONCE_REWRITE_TAC[ARITH_RULE `x < y <=> ~(y < x \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`X:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `N:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  POP_ASSUM MP_TAC;
  REAL_SIMP_TAC;
  STRIP_TAC;
  CLAIM `(z - X) * poly (poly_diff p) N < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - X`;
  LABEL_ALL_TAC;
  USE_THEN "Z-7" MP_TAC THEN REAL_ARITH_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC THEN REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  LABEL_ALL_TAC;
  USE_THEN "Z-6" (REWRITE_TAC o list);
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  CLAIM `&0 < poly p y - poly p z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-12" MP_TAC;
  USE_THEN "Z-5" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (y - z) * poly (poly_diff p) M`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  CLAIM `N < M`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`N:real`;`M:real`] (REWRITE_RULE[real_gt] POLY_IVT_POS));
  ASM_REWRITE_TAC[];
  DISCH_THEN (X_CHOOSE_TAC `K:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  (* save *)
  CLAIM `x < K /\  K < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `N`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `M`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  POP_ASSUM (ASSUME_TAC o GSYM);
  MP_TAC (ISPECL [`p:real list`;`X:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  REAL_SIMP_TAC;
  ONCE_REWRITE_TAC[REAL_ARITH `(x:real = y) <=> (y = x)`];
  ASM_REWRITE_TAC[REAL_ENTIRE];
  DISCH_THEN (X_CHOOSE_TAC `M:real`);
  POP_ASSUM MP_TAC THEN STRIP_TAC;
  LABEL_ALL_TAC;
  POP_ASSUM MP_TAC;
  USE_THEN "Z-5" MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `x < M /\  M < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `X`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
]);;

(* }}} *)

let neg_pos_neq_thm2 = prove_by_refinement(
  `!x y p. x < y ==> poly p x < &0 ==> poly p y > &0 ==>
            (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
            ?X. x < X /\ X < y /\
              (!z. (z = X) ==> (poly p z = &0)) /\
              (!z. x < z /\ z < X ==> poly p z < &0) /\
              (!z. X < z /\ z < y ==> poly p z > &0)`,
(* {{{ Proof *)
[
  REWRITE_TAC[real_gt];
  REPEAT STRIP_TAC;
  MP_TAC (ISPECL[`x:real`;`y:real`;`p:real list`] neg_pos_neq_thm);
  ASM_REWRITE_TAC[];
  REPEAT STRIP_TAC;
  EXISTS_TAC `X`;
  ASM_MESON_TAC[];
]);;
(* }}} *)


let lt_nz_thm = prove_by_refinement(
  `(!x. x1 < x /\ x < x2 ==> poly p x < &0) ==> (!x. x1 < x /\ x < x2 ==> ~(poly p x = &0))`,
(* {{{ Proof *)
[
  MESON_TAC[REAL_LT_NZ];
]);;
(* }}} *)

let gt_nz_thm = prove_by_refinement(
  `(!x. x1 < x /\ x < x2 ==> poly p x > &0) ==> (!x. x1 < x /\ x < x2 ==> ~(poly p x = &0))`,
(* {{{ Proof *)
[
  MESON_TAC[REAL_LT_NZ;real_gt];
]);;
(* }}} *)

let eq_eq_false_thm = prove_by_refinement(
  `!x y p. x < y ==> (poly p x = &0) ==> (poly p y = &0) ==>
       (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==> F`,
(* {{{ Proof *)

[
  REPEAT_N 3 STRIP_TAC;
  DISCH_THEN (fun x -> MP_TAC (MATCH_MP (ISPEC `p:real list` POLY_MVT) x) THEN ASSUME_TAC x);
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  CLAIM `poly p y - poly p x = &0`;
  REWRITE_TAC[real_sub];
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
  DISCH_THEN (REWRITE_ASSUMS o list);
  CLAIM `&0 < y - x`;
  USE_THEN "Z-6" MP_TAC THEN REAL_ARITH_TAC;
  POP_ASSUM (MP_TAC o ISPEC `x':real`);
  RULE_ASSUM_TAC GSYM;
  POP_ASSUM IGNORE THEN POP_ASSUM IGNORE;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  STRIP_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_LT_IMP_NZ];
]);;

(* }}} *)

let neg_zero_neg_thm = prove_by_refinement(
  `!x y p. x < y ==> poly p x < &0 ==> (poly p y = &0) ==>
     (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
     (!z. x < z /\ z < y ==> poly p z < &0)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[ARITH_RULE `x < y <=> ~(y <= x)`];
  REWRITE_TAC[ARITH_RULE `x <= y <=> (x < y \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p z - poly p x > &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-8" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) x' > &0`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  REWRITE_TAC[real_gt];
  ASM_REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) x' < &0`;
  REWRITE_TAC[REAL_MUL_LT];
  DISJ2_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[REAL_LT_ANTISYM];
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `&0 - poly p z < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(y - z) * poly (poly_diff p) x'' < &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REAL_ARITH_TAC;
  (* save *)
  CLAIM `x' < x''`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`x':real`;`x'':real`] (REWRITE_RULE[real_gt] POLY_IVT_NEG));
  REWRITE_ASSUMS[real_gt];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `x < x''' /\  x''' < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x'`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x''`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  MP_TAC  (ISPECL[`z:real`;`y:real`;`p:real list`] eq_eq_false_thm);
  POP_ASSUM (ASSUME_TAC o GSYM);
  ASM_REWRITE_TAC[];
  REPEAT_N 2 STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
]);;

(* }}} *)

let pos_zero_pos_thm = prove_by_refinement(
  `!x y p. x < y ==> poly p x > &0 ==> (poly p y = &0) ==>
     (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
     (!z. x < z /\ z < y ==> poly p z > &0)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[ARITH_RULE `x > y <=> ~(y >= x)`];
  REWRITE_TAC[ARITH_RULE `x >= y <=> (x > y \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p z - poly p x < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-8" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) x' < &0`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  REWRITE_TAC[real_gt];
  ASM_REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < (z - x) * poly (poly_diff p) x'`;
  REWRITE_TAC[REAL_MUL_GT];
  DISJ2_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[REAL_LT_ANTISYM];
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `&0 - poly p z > &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(y - z) * poly (poly_diff p) x'' > &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;];
  REPEAT STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REAL_ARITH_TAC;
  (* save *)
  CLAIM `x' < x''`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`x':real`;`x'':real`] (REWRITE_RULE[real_gt] POLY_IVT_POS));
  REWRITE_ASSUMS[real_gt];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `x < x''' /\  x''' < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x'`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x''`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  MP_TAC  (ISPECL[`z:real`;`y:real`;`p:real list`] eq_eq_false_thm);
  POP_ASSUM (ASSUME_TAC o GSYM);
  ASM_REWRITE_TAC[];
  REPEAT_N 2 STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
]);;

(* }}} *)

let zero_neg_neg_thm = prove_by_refinement(
  `!x y p. x < y ==> (poly p x = &0) ==> (poly p y < &0) ==>
     (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
     (!z. x < z /\ z < y ==> poly p z < &0)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[ARITH_RULE `x < y <=> ~(y <= x)`];
  REWRITE_TAC[ARITH_RULE `x <= y <=> (x < y \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p z - &0 > &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-3" MP_TAC;
  USE_THEN "Z-8" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) x' > &0`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  REWRITE_TAC[real_gt];
  ASM_REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;];
  REPEAT STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-8" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 > (z - x) * poly (poly_diff p) x'`;
  REWRITE_TAC[REAL_MUL_GT;real_gt;REAL_MUL_LT;];
  DISJ2_TAC;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[REAL_LT_ANTISYM];
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p y - poly p z < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-13" MP_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < y - z`;
  LABEL_ALL_TAC;
  USE_THEN "Z-11" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(y - z) * poly (poly_diff p) x'' < &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;];
  REPEAT STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REAL_ARITH_TAC;
  (* save *)
  CLAIM `x' < x''`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`x':real`;`x'':real`] (REWRITE_RULE[real_gt] POLY_IVT_NEG));
  REWRITE_ASSUMS[real_gt];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `x < x''' /\  x''' < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x'`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x''`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  MP_TAC  (ISPECL[`x:real`;`z:real`;`p:real list`] eq_eq_false_thm);
  POP_ASSUM (ASSUME_TAC o GSYM);
  ASM_REWRITE_TAC[];
  REPEAT_N 2 STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
]);;

(* }}} *)

let zero_pos_pos_thm = prove_by_refinement(
  `!x y p. x < y ==> (poly p x = &0) ==> (poly p y > &0) ==>
     (!z. x < z /\ z < y ==> ~(poly (poly_diff p) z = &0)) ==>
     (!z. x < z /\ z < y ==> poly p z > &0)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[ARITH_RULE `x > y <=> ~(y >= x)`];
  REWRITE_TAC[ARITH_RULE `x >= y <=> (x > y \/ (x = y))`];
  STRIP_TAC;
  MP_TAC (ISPECL [`p:real list`;`z:real`;`y:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p y - poly p z > &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-7" MP_TAC;
  USE_THEN "Z-3" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(y - z) * poly (poly_diff p) x' > &0`;
  REPEAT_N 2 (POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
  REWRITE_TAC[real_gt];
  ASM_REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;];
  REPEAT STRIP_TAC;
  LABEL_ALL_TAC;
  USE_THEN "Z-1" MP_TAC;
  USE_THEN "Z-7" MP_TAC;
  REAL_ARITH_TAC;
  (* save *)
  MP_TAC (ISPECL [`p:real list`;`x:real`;`z:real`] POLY_MVT);
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `poly p z - &0 < &0`;
  LABEL_ALL_TAC;
  USE_THEN "Z-9" MP_TAC;
  REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `&0 < z - x`;
  LABEL_ALL_TAC;
  USE_THEN "Z-12" MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `(z - x) * poly (poly_diff p) x'' < &0`;
  POP_ASSUM IGNORE;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REAL_ARITH_TAC;
  ASM_REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;];
  REPEAT STRIP_TAC;
  REPEAT_N 3 (POP_ASSUM MP_TAC);
  REAL_ARITH_TAC;
  (* save *)
  CLAIM `x'' < x'`;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  MP_TAC (ISPECL [`poly_diff p`;`x'':real`;`x':real`] (REWRITE_RULE[real_gt] POLY_IVT_POS));
  REWRITE_ASSUMS[real_gt];
  ASM_REWRITE_TAC[];
  STRIP_TAC;
  CLAIM `x < x''' /\  x''' < y`;
  STRIP_TAC;
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x''`;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `x'`;
  ASM_REWRITE_TAC[];
  ASM_MESON_TAC[];
  (* save *)
  MP_TAC  (ISPECL[`x:real`;`z:real`;`p:real list`] eq_eq_false_thm);
  POP_ASSUM (ASSUME_TAC o GSYM);
  ASM_REWRITE_TAC[];
  REPEAT_N 2 STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
  MATCH_MP_TAC REAL_LT_TRANS;
  EXISTS_TAC `z`;
  ASM_REWRITE_TAC[];
]);;

(* }}} *)
