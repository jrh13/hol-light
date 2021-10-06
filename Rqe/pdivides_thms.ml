let neg_odd_lem = prove_by_refinement(
  `!a n p c q d.
     (a pow n * p x = c x * q x + d x) ==>
     ODD n ==>
       ((-- a) pow n * p x = (-- c x) * q x + (-- d x))`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC;
  REWRITE_TAC[REAL_ARITH `-- x * y = -- (x * y)`];
  REWRITE_TAC[REAL_ARITH `-- x + -- y = -- (x + y)`];
  CLAIM `-- a pow n = -- (a pow n)`;
  DISJ_CASES_TAC (ARITH_RULE `a < &0 \/ (a = &0) \/ a > &0`);
  MP_TAC (ISPECL[`a:real`;`n:num`] REAL_POW_NEG);
  ASM_REWRITE_TAC[GSYM NOT_ODD];
  POP_ASSUM DISJ_CASES_TAC;
  ASM_REWRITE_TAC[real_pow];
  CLAIM `~(n = 0)`;
  ASM_MESON_TAC[ODD];
  STRIP_TAC;
  CLAIM `?n'. n = SUC n'`;
  ASM_MESON_TAC[num_CASES];
  STRIP_TAC;
  ASM_REWRITE_TAC[real_pow];
  REAL_ARITH_TAC;
  MP_TAC (ISPECL[`a:real`;`n:num`] REAL_POW_NEG);
  ASM_REWRITE_TAC[GSYM NOT_ODD];
  STRIP_TAC;
  ASM_REWRITE_TAC[];
  REWRITE_TAC[ARITH_RULE `-- x * y = -- (x * y)`];
  REWRITE_TAC[ARITH_RULE `(-- x = -- y) <=> (x = y)`];
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;

(* }}} *)

let mul_odd_lem = prove_by_refinement(
  `!a n p c q d.
     (a pow n * p x = c x * q x + d x) ==>
     ODD n ==>
       ((a * a pow n) * p x = (a * c x) * q x + (a * d x))`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  REWRITE_TAC[REAL_ARITH `(a * x) * y = a * (x * y)`];
  REWRITE_TAC[REAL_ARITH `a * x + a *  y = a *  (x + y)`];
  AP_TERM_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)
