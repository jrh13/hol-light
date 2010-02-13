(* ========================================================================= *)
(* Euclidean GCD algorithm.                                                  *)
(* ========================================================================= *)

needs "Library/prime.ml";;

let egcd = define
 `egcd(m,n) = if m = 0 then n
              else if n = 0 then m
              else if m <= n then egcd(m,n - m)
              else egcd(m - n,n)`;;

(* ------------------------------------------------------------------------- *)
(* Main theorems.                                                            *)
(* ------------------------------------------------------------------------- *)

let EGCD_INVARIANT = prove
 (`!m n d. d divides egcd(m,n) <=> d divides m /\ d divides n`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `m + n` THEN
  GEN_TAC THEN ONCE_REWRITE_TAC[egcd] THEN
  ASM_CASES_TAC `m = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  ASM_CASES_TAC `n = 0` THEN ASM_REWRITE_TAC[DIVIDES_0] THEN
  COND_CASES_TAC THEN
  (W(fun (asl,w) -> FIRST_X_ASSUM(fun th ->
    MP_TAC(PART_MATCH (lhs o snd o dest_forall o rand) th (lhand w)))) THEN
   ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
  ASM_MESON_TAC[DIVIDES_SUB; DIVIDES_ADD; SUB_ADD; LE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Hence we get the proper behaviour, and it's equal to the real GCD.        *)
(* ------------------------------------------------------------------------- *)

let EGCD_GCD = prove
 (`!m n. egcd(m,n) = gcd(m,n)`,
  ONCE_REWRITE_TAC[GSYM GCD_UNIQUE] THEN
  MESON_TAC[EGCD_INVARIANT; DIVIDES_REFL]);;

let EGCD = prove
 (`!a b. (egcd (a,b) divides a /\ egcd (a,b) divides b) /\
         (!e. e divides a /\ e divides b ==> e divides egcd (a,b))`,
  REWRITE_TAC[EGCD_GCD; GCD]);;
