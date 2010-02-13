let le_lem = prove_by_refinement(
 `(!y. y <= Y ==> P y) ==> 
  (!y. y < Y ==> P y) /\ 
  (!y. (y = Y) ==> P y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)


let lt_int_lem = prove_by_refinement(
 `(!y. y < Y ==> P y) ==> X < Y ==> 
  (!y. X < y /\ y < Y ==> P y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let ge_lem = prove_by_refinement(
 `(!y. Y <= y ==> P y) ==> 
  (!y. Y < y ==> P y) /\ 
  (!y. (y = Y) ==> P y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  POP_ASSUM MP_TAC THEN REAL_ARITH_TAC;
]);;
(* }}} *)

let gt_int_lem = prove_by_refinement(
 `(!y. Y < y ==> P y) ==> Y < X ==> 
  (!y. Y < y /\ y < X ==> P y)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  FIRST_ASSUM MATCH_ACCEPT_TAC;
]);;
(* }}} *)

let rest_lt_lem = prove_by_refinement(
  `Y < X ==> (!x. x < X ==> P x) ==> (!x. x < Y ==> P x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS;real_gt];
]);;
(* }}} *)

let rest_gt_lem = prove_by_refinement(
  `X < Y ==> (!x. X < x ==> P x) ==> (!x. Y < x ==> P x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS;real_gt];
]);;
(* }}} *)

let rest_eq_lt_lem = prove_by_refinement(
  `Y < X ==> (!x. x < X ==> P x) ==> (!x. (x = Y) ==> P x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
]);;
(* }}} *)

let rest_eq_gt_lem = prove_by_refinement(
  `X < Y ==> (!x. X < x ==> P x) ==> (!x. (x = Y) ==> P x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
]);;
(* }}} *)

let rest_int_lt_lem = prove_by_refinement(
  `Y < X ==> (!x. x < X ==> P x) ==> (!x. Y < x /\ x < X ==> P x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
]);;
(* }}} *)

let rest_int_gt_lem = prove_by_refinement(
  `X < Y ==> (!x. X < x ==> P x) ==> (!x. X < x /\ x < Y ==> P x)`,
(* {{{ Proof *)
[
  REPEAT STRIP_TAC;
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_MESON_TAC[REAL_LT_TRANS];
]);;
(* }}} *)


let INTERPSIGN_SUBSET = prove_by_refinement(
  `!P Q p s. interpsign P p s  /\ Q SUBSET P ==> interpsign Q p s`,
(* {{{ Proof *)
[
  REWRITE_TAC[SUBSET;IN];
  REPEAT_N 4 STRIP_TAC;
  STRUCT_CASES_TAC (ISPEC `s:sign` SIGN_CASES) THEN 
  REWRITE_TAC[interpsign] THEN MESON_TAC[];
]);; 
(* }}} *)

let INTERPSIGNS_SUBSET = prove_by_refinement(
  `!P Q ps ss. interpsigns ps P ss  /\ Q SUBSET P ==> interpsigns ps Q ss`,
(* {{{ Proof *)
[
  REWRITE_TAC[SUBSET;IN];
  REPEAT_N 2 STRIP_TAC;
  LIST_INDUCT_TAC;
  LIST_INDUCT_TAC;
  REWRITE_TAC[ALL2;interpsigns;interpsign];  
  REWRITE_TAC[ALL2;interpsigns;interpsign];  
  LIST_INDUCT_TAC;
  REWRITE_TAC[ALL2;interpsigns;interpsign];  
  REWRITE_TAC[ALL2;interpsigns;interpsign];  
  (* save *) 
  REPEAT STRIP_TAC;
  MATCH_MP_TAC INTERPSIGN_SUBSET;
  ASM_MESON_TAC[SUBSET;IN];
  REWRITE_ASSUMS[ALL2;interpsigns;interpsign];  
  FIRST_ASSUM MATCH_MP_TAC;
  ASM_REWRITE_TAC[];
]);; 
(* }}} *)

let NOPOINT_LEM = prove_by_refinement(
  `!pl sl. interpsigns pl (\x. T) sl  ==> 
   (interpsigns pl (\x. x < &0) sl  /\ 
    interpsigns pl (\x. x = &0) sl  /\ 
    interpsigns pl (\x. &0 < x) sl)`,
(* {{{ Proof *)

[
  REPEAT STRIP_TAC THEN MATCH_MP_TAC INTERPSIGNS_SUBSET THEN ASM_MESON_TAC[SUBSET;IN]
]);;

(* }}} *)
