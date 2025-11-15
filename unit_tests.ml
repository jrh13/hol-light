(* ========================================================================= *)
(*                          HOL LIGHT unit tests                             *)
(* ========================================================================= *)

let assert_conv conv tm tm' =
  let asl,etm = dest_thm(conv tm) in
  assert (asl = [] && is_eq etm && lhs etm = tm && rhs etm = tm');;

(* ------------------------------------------------------------------------- *)
(* Test verbose descriptive names for quantifiers/logical consts.            *)
(* ------------------------------------------------------------------------- *)

assert (`T` = `true`);;
assert (`F` = `false`);;
assert (`!(x:A). P x` = `forall (x:A). P x`);;
assert (`?(x:A). P x` = `exists (x:A). P x`);;
assert (`?!(x:A). P x` = `existsunique (x:A). P x`);;

(* ------------------------------------------------------------------------- *)
(* Test COMPUTE_CONVs.                                                       *)
(* ------------------------------------------------------------------------- *)

assert (rhs (concl (NUM_COMPUTE_CONV `if x then 1 + 2 else 3 + 4`))
              = `if x then 1 + 2 else 3 + 4`);;
assert (rhs (concl (NUM_COMPUTE_CONV `if true then 1 + 2 else 3 + 4`))
              = `3`);;
assert (rhs (concl (NUM_COMPUTE_CONV `\x. x + (1 + 2)`))
        = `\x. x + (1 + 2)`);;
assert (rhs (concl (NUM_COMPUTE_CONV `(\x. x + (1 + 2)) (3 + 4)`))
        = `10`);;
(* Arguments are reduced when the fn is a constant. *)
assert (rhs (concl (NUM_COMPUTE_CONV `(unknown_fn:num->num) (1+2)`))
        = `(unknown_fn:num->num) 3`);;

(* ------------------------------------------------------------------------- *)
(* Test list-specific evaluation conversions.                                *)
(* ------------------------------------------------------------------------- *)

assert_conv LIST_OF_SEQ_CONV
 `list_of_seq (\i. f(i + 17):B) 3` `[f (0 + 17):B; f (1 + 17); f (2 + 17)]`;;

assert_conv EL_CONV `EL 1 [0;1;2;3;4]` `1`;;

assert_conv LENGTH_CONV `LENGTH[1;2;3;4;5]` `5`;;

assert_conv REVERSE_CONV `REVERSE[a:X;b;c;d]` `[d:X;c;b;a]`;;

(* ------------------------------------------------------------------------- *)
(* Test basic_compset.                                                       *)
(* ------------------------------------------------------------------------- *)

let _ =
  let open Compute in
  let cs = basic_compset() in
  let cv = CBV_CONV cs in
  let wcv = WEAK_CBV_CONV cs in begin

  (* Generalized abstraction *)
  assert (rhs (concl (wcv `(\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))`)) =
          `1 + 2 + 3 + 4`);
  assert (rhs (concl (cv `(\((x,y),(z,w)). x + y + z + w) ((1,2),(3,4))`)) =
          `1 + 2 + 3 + 4`);

  (* Abstraction body is not reduced if WEAK_CBV is used *)
  assert (rhs (concl (wcv
          `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`)) =
        `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`);
  assert (rhs (concl (cv
          `(\((x,y),(z,w)):(num#num)#(num#num). true /\ true)`)) =
          `(\((x,y),(z,w)):(num#num)#(num#num). true)`);

  (* Match *)
  assert (
    rhs (concl (wcv `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`)) =
    `[3; 4; 5]`);
  assert (
    rhs (concl (cv `match [1;2;3;4;5] with [] -> [] | CONS x (CONS y z) -> z`)) =
    `[3; 4; 5]`);

  (* Let *)
  assert (rhs (concl (wcv `let x = 1 in x + 2`)) = `1 + 2`);
  assert (rhs (concl (cv `let x = 1 in x + 2`)) = `1 + 2`);
  end;;


(* ------------------------------------------------------------------------- *)
(* Test benign redefinition when polymorphic type is involved.               *)
(* ------------------------------------------------------------------------- *)

let _ = define `(h_benign:A list -> num) [] = 0 /\
                h_benign (CONS _ t) = 1 + h_benign t`;;
let _ = define `(h_benign:A list -> num) [] = 0 /\
                h_benign (CONS _ t) = 1 + h_benign t`;;


(* ------------------------------------------------------------------------- *)
(* Test benign redefinition of an inductive datatype.                        *)
(* ------------------------------------------------------------------------- *)

let _ = new_inductive_definition
  `(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (forall s s'' n. (exists s'. step s s' /\ steps step n s' s'')
      ==> steps step (n+1) s s'')`;;
let _ = new_inductive_definition
  `(forall s. steps (step:S->S->bool) 0 (s:S) (s:S)) /\
   (forall s s'' n. (exists s'. step s s' /\ steps step n s' s'')
      ==> steps step (n+1) s s'')`;;


(* ------------------------------------------------------------------------- *)
(* Test the 'er' command of the subgoal package.                             *)
(* Each test case has a proof in the THEN form, followed by g-e(er) form.    *)
(* ------------------------------------------------------------------------- *)

(* case 1: 'er' has to rotate 1 subgoal *)
prove(`x + 1 = 1 + x /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        ALL_TAC;
        ARITH_TAC
    ] THEN REWRITE_TAC[ADD_SYM]);;
g `x + 1 = 1 + x /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(ALL_TAC);; (* rotates 1 subgoal *)
	e(ARITH_TAC);;
e(REWRITE_TAC[ADD_SYM]);;
top_thm();;

(* case 2: 'er' has to rotate 2 subgoals *)
prove(`(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        CONJ_TAC;
        ARITH_TAC
    ] THEN REWRITE_TAC[ADD_AC]);;
g `(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(CONJ_TAC);; (* rotates 2 subgoals *)
	e(ARITH_TAC);;
e(REWRITE_TAC[ADD_AC]);;
e(REWRITE_TAC[ADD_AC]);;
top_thm();;

(* case 2': 'er' has to rotate 2 subgoals. There is b(). *)
prove(`(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        CONJ_TAC;
        ARITH_TAC
    ] THEN REWRITE_TAC[ADD_AC]);;
g `(x + 1 = 1 + x /\ (x + y) + z = x + (y + z)) /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(CONJ_TAC);; (* rotates 2 subgoals *)
	b();;
	er(CONJ_TAC);; (* rotates 2 subgoals *)
	e(ARITH_TAC);;
e(REWRITE_TAC[ADD_AC]);;
e(REWRITE_TAC[ADD_AC]);;
top_thm();;

(* case 3: 'er' has to rotate 0 subgoal *)
prove(`x + 1 = 1 + x /\ 1 + 1 = 2`,
    CONJ_TAC THENL [
        ARITH_TAC;
        ARITH_TAC
    ]);;
g `x + 1 = 1 + x /\ 1 + 1 = 2`;;
e(CONJ_TAC);;
	er(ARITH_TAC);; (* does not rotate since ARITH_TAC discharges the subgoal *)
	e(ARITH_TAC);;
top_thm();;


(* ------------------------------------------------------------------------- *)
(* Test that e() finds same variable names with different types()            *)
(* ------------------------------------------------------------------------- *)

g `(f:num->A) (x:num) = f 1`;;
try
  e (SUBGOAL_THEN `x = true` ASSUME_TAC);
  assert false;
with Failure _ -> () | Assert_failure _ as e -> raise e;;


(* ------------------------------------------------------------------------- *)
(* Test functions in lib.                                                    *)
(* ------------------------------------------------------------------------- *)

assert (find_index ((=) 10) [0;10;20] = Some 1);;
assert (find_index ((=) 99) [0;10;20] = None);;
assert (index 10 [0;10;20] = 1);;
assert (not (can (index 99) [0;10;20]));;


(* ------------------------------------------------------------------------- *)
(* Test bignum.                                                              *)
(* ------------------------------------------------------------------------- *)

(* Z.pow (Z.of_int 0) 0 is 1.
   Num.power_num (Num.num_of_int 0) (Num.num_of_int 0) is also 1. *)
assert (power_num (num 0) (num 0) = num 1);;
assert (pow (num 0) 0 = num 1);;

assert (power_num (num 2) (num 3) = num 8);;
assert (power_num (num 1 // num 2) (num 3) = (num 1 // num 8));;
assert (power_num (num 1 // num 2) (num 4) = (num 1 // num 16));;
assert (power_num (num 1 // num 2) (num (-3)) = num 8);;
assert (power_num (num 1 // num 2) (num (-4)) = num 16);;
assert (power_num (num 1 // num 2) (num 0) = num 1);;
assert (pow (num 2) 3 = num 8);;
assert (pow (num 1 // num 2) 3 = (num 1 // num 8));;
assert (pow (num 1 // num 2) 4 = (num 1 // num 16));;
assert (pow (num 1 // num 2) (-3) = num 8);;
assert (pow (num 1 // num 2) (-4) = num 16);;
assert (pow (num 1 // num 2) 0 = num 1);;


(* ------------------------------------------------------------------------- *)
(* Test check_axioms.                                                        *)
(* ------------------------------------------------------------------------- *)

new_axiom `k = 1`;;
try
  check_axioms (); (* check_axioms must raise Failure *)
  assert false;
with Failure _ -> () | Assert_failure _ as e -> raise e;;
