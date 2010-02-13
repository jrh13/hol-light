let empty_mat = prove_by_refinement(
   `interpmat [] [] [[]]`,
(* {{{ Proof *)

[
  REWRITE_TAC[interpmat;ROL_EMPTY;interpsigns;ALL2;partition_line];
]);;

(* }}} *)

let empty_sgns = [ARITH_RULE `&1 > &0`];;

let monic_isign_lem = prove(
  `(!s c mp p. (!x. c * p x = mp x) ==> c > &0 ==> interpsign s mp Pos ==> interpsign s p Pos) /\  
   (!s c mp p. (!x. c * p x = mp x) ==> c < &0 ==> interpsign s mp Pos ==> interpsign s p Neg) /\  
   (!s c mp p. (!x. c * p x = mp x) ==> c > &0 ==> interpsign s mp Neg ==> interpsign s p Neg) /\  
   (!s c mp p. (!x. c * p x = mp x) ==> c < &0 ==> interpsign s mp Neg ==> interpsign s p Pos) /\  
   (!s c mp p. (!x. c * p x = mp x) ==> c > &0 ==> interpsign s mp Zero ==> interpsign s p Zero) /\  
   (!s c mp p. (!x. c * p x = mp x) ==> c < &0 ==> interpsign s mp Zero ==> interpsign s p Zero)`,
(* {{{ Proof *)

  REWRITE_TAC[interpsign] THEN REPEAT STRIP_TAC THEN 
  POP_ASSUM (fun x -> POP_ASSUM (fun y -> MP_TAC (MATCH_MP y x))) THEN 
  POP_ASSUM MP_TAC THEN 
  POP_ASSUM (ASSUME_TAC o GSYM o (ISPEC `x:real`)) THEN 
  ASM_REWRITE_TAC[REAL_MUL_LT;REAL_MUL_GT;real_gt;REAL_ENTIRE] THEN 
  REAL_ARITH_TAC);;

(* }}} *)

let gtpos::ltpos::gtneg::ltneg::gtzero::ltzero::[] = CONJUNCTS monic_isign_lem;;  

let main_lem000 = prove_by_refinement(
  `!l n. (LENGTH l = SUC n) ==> 0 < LENGTH l`,
(* {{{ Proof *)

[
  LIST_INDUCT_TAC;
  REWRITE_TAC[LENGTH];
  ARITH_TAC;
  ARITH_TAC;
]);;

(* }}} *)

let main_lem001 = prove_by_refinement(
  `x <> &0 ==> (LAST l = x) ==> LAST l <> &0`,
[MESON_TAC[]]);;

let main_lem002 = prove_by_refinement(
  `(x <> y ==> x <> y) /\ 
   (x < y ==> x <> y) /\ 
   (x > y ==> x <> y) /\ 
   (~(x >= y) ==> x <> y) /\ 
   (~(x <= y) ==> x <> y) /\ 
   (~(x = y) ==> x <> y)`,
(* {{{ Proof *)

[
  REWRITE_TAC[NEQ] THEN REAL_ARITH_TAC
]);;

(* }}} *)

let factor_pos_pos = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Pos ==> interpsign s p Pos ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Pos`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;real_gt];
  DISJ2_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt];
]);;
(* }}} *)

let factor_pos_neg = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Pos ==> interpsign s p Neg ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Neg`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_LT;real_gt];
  DISJ2_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt];
]);;
(* }}} *)

let factor_pos_zero = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Pos ==> interpsign s p Zero ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Zero`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_LT;REAL_ENTIRE;real_gt];
]);;
(* }}} *)

let factor_zero_pos = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Zero ==> interpsign s p Pos ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Zero`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;REAL_ENTIRE];
  DISJ1_TAC;
  ASM_MESON_TAC[POW_0;num_CASES;];
]);;
(* }}} *)

let factor_zero_neg = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Zero ==> interpsign s p Neg ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Zero`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;REAL_ENTIRE];
  DISJ1_TAC;
  ASM_MESON_TAC[POW_0;num_CASES;];
]);;
(* }}} *)

let factor_zero_zero = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Zero ==> interpsign s p Zero ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Zero`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REAL_ARITH_TAC;
]);;
(* }}} *)

let factor_neg_even_pos = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Pos ==> EVEN k ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Pos`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt];
  DISJ2_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;PARITY_POW_LT];
]);;
(* }}} *)

let factor_neg_even_neg = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Neg ==> EVEN k ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Neg`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt];
  DISJ2_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;PARITY_POW_LT];
]);;
(* }}} *)

let factor_neg_even_zero = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Zero ==> EVEN k ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Zero`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;REAL_ENTIRE];
]);;
(* }}} *)

let factor_neg_odd_pos = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Pos ==> ODD k ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Neg`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;REAL_ENTIRE];
  DISJ1_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;PARITY_POW_LT];  
]);;
(* }}} *)

let factor_neg_odd_neg = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Neg ==> ODD k ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Pos`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;REAL_ENTIRE];
  DISJ1_TAC;
  ASM_MESON_TAC[REAL_POW_LT;real_gt;PARITY_POW_LT];  
]);;
(* }}} *)

let factor_neg_odd_zero = prove_by_refinement(
  `interpsign s (\x. &0 + x * &1) Neg ==> interpsign s p Zero ==> ODD k ==> ~(k = 0) ==> 
   (!x. x pow k * p x = q x) ==> interpsign s q Zero`,
(* {{{ Proof *)
[
  REWRITE_TAC[interpsign;REAL_ADD_LID;REAL_MUL_RID;];
  REPEAT STRIP_TAC;
  POP_ASSUM (fun x -> (RULE_ASSUM_TAC (fun y -> try MATCH_MP y x with _ -> y)));
  POP_ASSUM (ASSUME_TAC o ISPEC rx o GSYM);
  ASM_REWRITE_TAC[];
  REWRITE_TAC[REAL_MUL_GT;REAL_MUL_LT;real_gt;REAL_ENTIRE];
]);;
(* }}} *)
