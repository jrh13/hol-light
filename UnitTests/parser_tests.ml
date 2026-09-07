(* ========================================================================= *)
(*                   HOL Light parser and typechecker tests                  *)
(*                                                                           *)
(*  Checks that quotations are parsed and typechecked into the expected       *)
(*  terms, exercising the preterm typing pass in preterm.ml (variable versus  *)
(*  constant resolution, varstructs, type annotations, interface mapping).    *)
(*                                                                           *)
(*  Run via:                                                                 *)
(*    make UnitTests/parser_tests.byte && ./UnitTests/parser_tests.byte      *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A binder may shadow a constant of the same name, even when type-annotated *)
(* or part of a tuple varstruct (see varstruct_consts and the Absp branch in *)
(* preterm.ml). Without the fix the first quotation below raises             *)
(* "shadow_test_const has type bool, it cannot be used with type num".       *)
(* ------------------------------------------------------------------------- *)

let _ = new_definition `shadow_test_const = T`;;   (* a constant of type bool *)

(* An annotated binder shadows the constant: the bound variable has the      *)
(* annotated type, not the constant's bool type.                             *)
let () =
  let tm = `forall (shadow_test_const:num). shadow_test_const > 0` in
  let v = bndvar (rand tm) in
  assert (is_var v && type_of v = `:num`);;

(* Tuple varstructs are handled too. *)
assert (aconv `\(shadow_test_const:num,y:num). shadow_test_const + y`
              `\(a:num,b:num). a + b`);;

(* A free occurrence of the same name still resolves to the constant. *)
assert (is_const
  (lhand `shadow_test_const /\ (?(shadow_test_const:num). shadow_test_const > 0)`));;

(* The same holds for an interface or overloaded name such as "gcd" or "sum",  *)
(* which is not itself a constant but is still parsed as one.                  *)

let _ = new_definition `shadow_test_num (n:num) = n + 1`;;
make_overloadable "shadow_test_op" `:A->A`;;
overload_interface("shadow_test_op",`shadow_test_num`);;

assert (is_abs `\shadow_test_op. T`);;
assert (aconv `\(shadow_test_op:num). shadow_test_op + 1` `\(x:num). x + 1`);;
assert (aconv `\(shadow_test_op:num,y:num). shadow_test_op + y`
              `\(a:num,b:num). a + b`);;
assert (is_const (rator (lhand
  `shadow_test_op (x:num) = (\shadow_test_op. shadow_test_op) x`)));;

(* With the flag off, such a binder is a degenerate generalized abstraction. *)
let () =
  ignore_constant_varstruct := false;
  assert (not(is_abs `\shadow_test_const. T`) &&
          not(is_abs `\shadow_test_op. T`));
  ignore_constant_varstruct := true;;
