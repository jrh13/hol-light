(* ========================================================================= *)
(* Iterated application of a function, ITER n f x = f^n(x).                  *)
(*                                                                           *)
(* (c) Marco Maggesi, Graziano Gentili and Gianni Ciolli, 2008.              *)
(* ========================================================================= *)

let ITER = define
  `(!f. ITER 0 f x = x) /\
   (!f n. ITER (SUC n) f x = f (ITER n f x))`;;

let ITER_POINTLESS = prove
  (`(!f. ITER 0 f = I) /\
    (!f n. ITER (SUC n) f = f o ITER n f)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM; o_THM; ITER]);;

let ITER_ALT = prove
  (`(!f x. ITER 0 f x = x) /\
    (!f n x. ITER (SUC n) f x = ITER n f (f x))`,
   REWRITE_TAC [ITER] THEN GEN_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC [ITER]);;

let ITER_ALT_POINTLESS = prove
  (`(!f. ITER 0 f = I) /\
    (!f n. ITER (SUC n) f = ITER n f o f)`,
   REWRITE_TAC [FUN_EQ_THM; I_THM; o_THM; ITER_ALT]);;

let ITER_ADD = prove
  (`!f n m x. ITER n f (ITER m f x) = ITER (n + m) f x`,
   GEN_TAC THEN INDUCT_TAC THEN ASM_REWRITE_TAC[ITER; ADD]);;

let ITER_MUL = prove
  (`!f n m x. ITER n (ITER m f) x = ITER (n * m) f x`,
   GEN_TAC THEN INDUCT_TAC THEN
   ASM_REWRITE_TAC[ITER; MULT; ITER_ADD; ADD_AC]);;

let ITER_FIXPOINT = prove
  (`!f n x. f x = x ==> ITER n f x = x`,
   GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC [ITER_ALT]);;
