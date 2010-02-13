let EVEN_DIV_LEM = prove_by_refinement(
  `!set p q c d a n. 
     (!x. a pow n * p x = c x * q x + d x) ==> 
     a <> &0 ==> 
     EVEN n ==>               
       ((interpsign set q Zero) ==> 
        (interpsign set d Neg)  ==> 
         (interpsign set p Neg)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set d Pos)  ==> 
         (interpsign set p Pos)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set d Zero)  ==> 
         (interpsign set p Zero))`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpsign];
  REPEAT STRIP_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `&0 < a pow n`; 
  ASM_MESON_TAC[EVEN_ODD_POW;real_gt];
  STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `&0 < a pow n`; 
  ASM_MESON_TAC[EVEN_ODD_POW;real_gt];
  STRIP_TAC;
  CLAIM `a pow n * p x > &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `&0 < a pow n`; 
  ASM_MESON_TAC[EVEN_ODD_POW;real_gt];
  STRIP_TAC;
  CLAIM `a pow n * p x = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_POS_NZ];
]);;

(* }}} *)

let GT_DIV_LEM = prove_by_refinement(
  `!set p q c d a n. 
     (!x. a pow n * p x = c x * q x + d x) ==> 
     a > &0 ==> 
       ((interpsign set q Zero) ==> 
        (interpsign set d Neg)  ==> 
         (interpsign set p Neg)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set d Pos)  ==> 
         (interpsign set p Pos)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set d Zero)  ==> 
         (interpsign set p Zero))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign];
  REPEAT_N 9 STRIP_TAC;
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;];
  STRIP_TAC;
  REPEAT STRIP_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  (* save *) 
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `a pow n * p x > &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `a pow n * p x = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
]);;
(* }}} *)

let NEG_ODD_LEM = prove_by_refinement(
  `!set p q c d a n. 
     (!x. a pow n * p x = c x * q x + d x) ==> 
     a < &0 ==>
     ODD n ==>  
       ((interpsign set q Zero) ==> 
        (interpsign set (\x. -- d x) Neg)  ==> 
         (interpsign set p Neg)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set (\x. -- d x) Pos)  ==> 
         (interpsign set p Pos)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set (\x. -- d x) Zero)  ==> 
         (interpsign set p Zero))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;POLY_NEG];
  REPEAT_N 10 STRIP_TAC;
  CLAIM `a pow n < &0`;
  ASM_MESON_TAC[PARITY_POW_LT;real_gt;];
  STRIP_TAC;
  REAL_SIMP_TAC;
  REPEAT STRIP_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `a pow n * p x > &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  (* save *) 
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `a pow n * p x = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
]);;
(* }}} *)

let NEQ_ODD_LEM = prove_by_refinement(
  `!set p q c d a n. 
     (!x. a pow n * p x = c x * q x + d x) ==> 
     a <> &0 ==>
     ODD n ==>  
       ((interpsign set q Zero) ==> 
        (interpsign set (\x. a * d x) Neg)  ==> 
         (interpsign set p Neg)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set (\x. a * d x) Pos)  ==> 
         (interpsign set p Pos)) /\ 
       ((interpsign set q Zero) ==> 
        (interpsign set (\x. a * d x) Zero)  ==> 
         (interpsign set p Zero))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;POLY_CMUL];
  REPEAT_N 10 STRIP_TAC;
  CLAIM `a < &0 \/ a > &0 \/ (a = &0)`;
  REAL_ARITH_TAC;
  REWRITE_ASSUMS[NEQ];
  ASM_REWRITE_TAC[];
  LABEL_ALL_TAC;
  STRIP_TAC;
  (* save *) 
  CLAIM `a pow n < &0`;
  ASM_MESON_TAC[PARITY_POW_LT];
  STRIP_TAC;
  REPEAT STRIP_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `d x > &0`;
  POP_ASSUM MP_TAC;
  ASM_REWRITE_TAC[real_gt;REAL_MUL_LT];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  CLAIM `&0 < a pow n * p x`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_GT];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  (* save *) 
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `d x < &0`;
  POP_ASSUM MP_TAC;
  REWRITE_TAC[REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `d x = &0`;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
  STRIP_TAC;
  CLAIM `a pow n * p x = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
  (* save *) 
  CLAIM `a pow n > &0`;
  ASM_MESON_TAC[EVEN_ODD_POW;NEQ;real_gt];
  STRIP_TAC;
  REPEAT STRIP_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `d x < &0`;
  POP_ASSUM MP_TAC;
  ASM_REWRITE_TAC[real_gt;REAL_MUL_LT];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  POP_ASSUM MP_TAC;
  POP_ASSUM MP_TAC;
  REWRITE_TAC[REAL_MUL_LT];
  REPEAT STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  (* save *) 
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `d x > &0`;
  POP_ASSUM MP_TAC;
  REWRITE_TAC[REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  CLAIM `a pow n * p x < &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  STRIP_TAC;
  CLAIM `a pow n * p x > &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt];
  REPEAT STRIP_TAC;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  RULE_ASSUM_TAC (fun y -> try ISPEC `x:real` y with _ -> y);
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x]);
  POP_ASSUM MP_TAC;
  POP_ASSUM (fun x -> REWRITE_ASSUMS[x;REAL_MUL_RZERO;REAL_ADD_LID;]);
  STRIP_TAC;
  CLAIM `d x = &0`;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
  STRIP_TAC;
  CLAIM `a pow n * p x = &0`;
  EVERY_ASSUM MP_TAC THEN REAL_ARITH_TAC;
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
]);;
(* }}} *)

let NEQ_MULT_LT_LEM = prove_by_refinement(
  `!a q d d' set. 
     a < &0 ==>
       ((interpsign set d Neg)  ==> 
        (interpsign set (\x. a * d x) Pos)) /\ 
       ((interpsign set d Pos)  ==> 
         (interpsign set (\x. a * d x) Neg)) /\ 
       ((interpsign set d Zero)  ==> 
         (interpsign set (\x. a * d x) Zero))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;POLY_NEG];
  REPEAT STRIP_TAC;
  ASM_MESON_TAC[REAL_MUL_GT;real_gt];  
  ASM_MESON_TAC[REAL_MUL_LT;real_gt];  
  ASM_MESON_TAC[REAL_ENTIRE;REAL_NOT_EQ;real_gt];
]);;
(* }}} *)

let NEQ_MULT_GT_LEM = prove_by_refinement(
  `!a q d d' set. 
     a > &0 ==>
       ((interpsign set d Neg)  ==> 
         (interpsign set (\x. a * d x) Neg)) /\ 
       ((interpsign set d Pos)  ==> 
         (interpsign set (\x. a * d x) Pos)) /\ 
       ((interpsign set d Zero)  ==> 
         (interpsign set (\x. a * d x) Zero))`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;POLY_NEG] THEN 
  MESON_TAC[REAL_MUL_LT;REAL_ENTIRE;REAL_NOT_EQ;REAL_MUL_GT;real_gt];  
]);;
(* }}} *)

let unknown_thm = prove(
  `!set p. (interpsign set p Unknown)`,
    MESON_TAC[interpsign]);;

let ips_gt_nz_thm = prove_by_refinement(
  `!x. x > &0 ==> x <> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[NEQ];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let ips_lt_nz_thm = prove_by_refinement(
  `!x. x < &0 ==> x <> &0`,
(* {{{ Proof *)
[
  REWRITE_TAC[NEQ];
  REAL_ARITH_TAC;
]);;
(* }}} *)
