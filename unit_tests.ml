(* ========================================================================= *)
(*                          HOL LIGHT unit tests                             *)
(* ========================================================================= *)

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
(* Test check_axioms.                                                        *)
(* ------------------------------------------------------------------------- *)

new_axiom `k = 1`;;
try
  check_axioms (); (* check_axioms must raise Failure *)
  assert false;
with Failure _ -> () | Assert_failure _ as e -> raise e;;
