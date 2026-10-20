(* ========================================================================= *)
(* 4CT/dyck.ml                                                               *)
(*                                                                           *)
(* dyck.v: Dyck numbers.  gen_dyck m n counts the balanced bracket word      *)
(* fragments of length n with m-1 extra closing brackets, and dyck n =       *)
(* gen_dyck 1 n counts the balanced words of length n (the Catalan numbers   *)
(* at even n, 0 at odd n).  Dyck numbers are the numerical link between the  *)
(* initial colour tree (initctree.ml) and the initial chromogram tree        *)
(* (initgtree.ml), which both store dyck (count_cbit1 (ctrace et)) at each   *)
(* admissible trace et.                                                      *)
(* ========================================================================= *)

(* gen_dyck m n recurses on n with m as a varying parameter, so we use the   *)
(* curried higher-order form (num_RECURSION on n) and a plain wrapper. Coq:  *)
(* match n, m with 0,1 => 1 | n'.+1,m'.+1 => gen_dyck m.+1 n' +              *)
(*      gen_dyck m' n' | _,_ => 0.                                           *)

let gen_dyck_fn = new_recursive_definition num_RECURSION
 `(gen_dyck_fn 0 = (\m. if m = 1 then 1 else 0)) /\
  (gen_dyck_fn (SUC n) =
     (\m. if m = 0 then 0 else gen_dyck_fn n (SUC m) + gen_dyck_fn n (m - 1)))`
     ;;

let gen_dyck = new_definition
 `gen_dyck m n = gen_dyck_fn n m`;;

let dyck = new_definition
 `dyck n = gen_dyck 1 n`;;

(* The recursion with a nonzero first argument, and gen_dyck 0 = 0.          *)
let GEN_DYCK_SHIFT = prove
 (`!m n. gen_dyck (SUC m) (SUC n) = gen_dyck (SUC(SUC m)) n + gen_dyck m n`,
  REWRITE_TAC[gen_dyck; gen_dyck_fn; NOT_SUC; SUC_SUB1]);;

let GEN_DYCK_0 = prove
 (`!n. gen_dyck 0 n = 0`,
  INDUCT_TAC THEN REWRITE_TAC[gen_dyck; gen_dyck_fn] THEN ARITH_TAC);;

(* gen_dyck m n vanishes once n+1 < m (not enough length to close m          *)
(* brackets).                                                                *)
let GEN_DYCK_MAX = prove
 (`!n m. n + 1 < m ==> gen_dyck m n = 0`,
  REWRITE_TAC[gen_dyck] THEN INDUCT_TAC THEN
  REWRITE_TAC[gen_dyck_fn] THEN GEN_TAC THENL
   [ARITH_TAC;
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `gen_dyck_fn n (SUC m) = 0 /\ gen_dyck_fn n (m - 1) = 0`
     (fun th -> REWRITE_TAC[th; ADD_CLAUSES]) THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC]);;

(* Exactly one balanced fragment of length m closes m+1 brackets:            *)
(* all-closes.                                                               *)
let GEN_DYCK_ALL_CLOSE = prove
 (`!m. gen_dyck (SUC m) m = 1`,
  INDUCT_TAC THEN ASM_REWRITE_TAC[GEN_DYCK_SHIFT] THENL
   [REWRITE_TAC[gen_dyck; gen_dyck_fn; ARITH];
    SIMP_TAC[GEN_DYCK_MAX; ARITH_RULE `m + 1 < SUC(SUC(SUC m))`;
             ADD_CLAUSES]]);;

(* Generalised positivity: there is always a balanced fragment of even       *)
(* excess length. even_dyck_pos is the k = 0 instance.                       *)
let GEN_DYCK_POS = prove
 (`!n k. 0 < gen_dyck (SUC k) (2 * n + k)`,
  INDUCT_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES; GEN_DYCK_ALL_CLOSE; ARITH];
    REWRITE_TAC[ARITH_RULE `2 * SUC n + k = SUC(2 * n + SUC k)`;
                GEN_DYCK_SHIFT] THEN
    MATCH_MP_TAC(ARITH_RULE `0 < a ==> 0 < a + b`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `SUC k`) THEN REWRITE_TAC[]]);;

let EVEN_DYCK_POS = prove
 (`!n. 0 < dyck (2 * n)`,
  GEN_TAC THEN REWRITE_TAC[dyck] THEN
  MP_TAC(SPECL [`n:num`; `0`] GEN_DYCK_POS) THEN
  REWRITE_TAC[ADD_CLAUSES; ARITH]);;
