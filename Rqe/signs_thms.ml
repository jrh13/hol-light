let [pth_0g;pth_0l;pth_gg;pth_gl;pth_lg;pth_ll] = 
   (CONJUNCTS o prove)
   (`((p = &0) ==> c > &0 ==> (c * p = &0)) /\
     ((p = &0) ==> c < &0 ==> (c * p = &0)) /\
     (p > &0 ==> c > &0 ==> c * p > &0) /\
     (p > &0 ==> c < &0 ==> c * p < &0) /\
     (p < &0 ==> c > &0 ==> c * p < &0) /\
     (p < &0 ==> c < &0 ==> c * p > &0)`,
    SIMP_TAC[REAL_MUL_RZERO] THEN                          
    REWRITE_TAC[REAL_ARITH `(x > &0 <=> &0 < x) /\ (x < &0 <=> &0 < --x)`;
                REAL_ARITH `~(p = &0) <=> p < &0 \/ p > &0`] THEN
    REWRITE_TAC[IMP_IMP] THEN
    REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP REAL_LT_MUL) THEN
    REAL_ARITH_TAC);;

let pth_nzg = prove_by_refinement(
  `p <> &0 ==> c > &0 ==> c * p <> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[NEQ;REAL_ENTIRE] THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let pth_nzl = prove_by_refinement(
  `p <> &0 ==> c < &0 ==> c * p <> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[NEQ;REAL_ENTIRE] THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let signs_lem01 = prove_by_refinement(
  `c < &0 ==> p < &0 ==> (c * p = p') ==> p' > &0`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
]);;
(* }}} *)

let signs_lem02 = prove_by_refinement(
  `c > &0 ==> p < &0 ==> (c * p = p') ==> p' < &0`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
]);;
(* }}} *)

let signs_lem03 = prove_by_refinement(
  `c < &0 ==> p > &0 ==> (c * p = p') ==> p' < &0`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
]);;
(* }}} *)

let signs_lem04 = prove_by_refinement(
  `c > &0 ==> p > &0 ==> (c * p = p') ==> p' > &0`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
]);;
(* }}} *)

let signs_lem05 = prove_by_refinement(
  `c < &0 ==> (p = &0) ==> (c * p = p') ==> (p' = &0)`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt;REAL_MUL_RZERO];
]);;
(* }}} *)

let signs_lem06 = prove_by_refinement(
  `c > &0 ==> (p = &0) ==> (c * p = p') ==> (p' = &0)`,
(* {{{ Proof *)
[
  ASM_MESON_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt;REAL_MUL_RZERO];
]);;
(* }}} *)

let signs_lem07 = prove_by_refinement(
  `c < &0 ==> p <> &0 ==> (c * p = p') ==> p' <> &0`,
(* {{{ Proof *)

[
  ASM_MESON_TAC[NEQ;REAL_MUL_LT;REAL_MUL_GT;real_gt;REAL_MUL_RZERO;REAL_ENTIRE;REAL_GT_IMP_NZ];
]);;

(* }}} *)

let signs_lem08 = prove_by_refinement(
  `c > &0 ==> p <> &0 ==> (c * p = p') ==> p' <> &0`,
(* {{{ Proof *)

[
  ASM_MESON_TAC[NEQ;REAL_MUL_LT;REAL_MUL_GT;real_gt;REAL_MUL_RZERO;REAL_ENTIRE;REAL_LT_IMP_NZ];
]);;

(* }}} *)

let signs_lem002 = prove_by_refinement(
  `!p. (p = &0) \/ (p <> &0)`,
(* {{{ Proof *)
[
  MESON_TAC[NEQ];
]);;
(* }}} *)

let signs_lem003 = TAUT `a \/ b ==> (a ==> x) ==> (b ==> y) ==> (a /\ x \/ b /\ y)`;;

let sz_z_thm = ref TRUTH;;
let sz_nz_thm = ref TRUTH;;

let PULL_CASES_THM = prove
 (`!a p p0 p1.
((a = &0) /\ (p <=> p0) \/ (a <> &0) /\ (p <=> p1)) <=> ((p <=> (a = &0) /\ p0 \/ a <> &0 /\ p1 ))`,
(* {{{ Proof *)
   REPEAT STRIP_TAC THEN  REWRITE_TAC[NEQ] THEN MAP_EVERY BOOL_CASES_TAC [`p:bool`; `p0:bool`; `p1:bool`; `p2:bool`] THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;
(* }}} *)

let signs_lem0002 = prove(
  `!p. p <> &0 ==> (p > &0) \/ (p < &0)`,REWRITE_TAC [NEQ] THEN REAL_ARITH_TAC);;
let signs_lem0003 = TAUT `a \/ b ==> (a ==> x) ==> (b ==> y) ==> (a /\ x \/ b /\ y)`;;

let PULL_CASES_THM_NZ = prove
 (`!a p p1 p2.
  (a <> &0) ==> ((a > &0 /\ (p <=> p1) \/ a < &0 /\ (p <=> p2)) <=>
   ((p <=> a > &0 /\ p1 \/ a < &0 /\ p2)))`,
(* {{{ Proof *)
   REWRITE_TAC[NEQ] THEN
   REPEAT STRIP_TAC THEN  
   REWRITE_TAC[NEQ] THEN
   MAP_EVERY BOOL_CASES_TAC [`p:bool`; `p0:bool`; `p1:bool`; `p2:bool`] THEN
   ASM_REWRITE_TAC[] THEN TRY (POP_ASSUM MP_TAC THEN REAL_ARITH_TAC)
);;
(* }}} *)
