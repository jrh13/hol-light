(* ========================================================================= *)
(*             HOL LIGHT unit tests for record types                         *)
(*                                                                           *)
(* Tests for Library/components.ml and Library/records.ml.                    *)
(* ========================================================================= *)

needs "Library/records.ml";;

let point_INDUCT,point_RECURSION,point_COMPONENTS =
  define_auto_record_type
   "test_point = { xcoord: num; ycoord: num }";;

(* Check that the induction, recursion and component theorems exist *)
let _ = concl point_INDUCT;;
let _ = concl point_RECURSION;;
let _ = concl point_COMPONENTS;;

(* Check that read/write theorems were generated *)
assert (length (get_record_components point_COMPONENTS) = 2);;

(* Check read-write laws *)
let rw_thms = record_read_write_thms (point_INDUCT, point_COMPONENTS);;
assert (length rw_thms = 2);;

(* Check strongly_valid_component theorems *)
let sv_thms =
  record_strongly_valid_component_thms (point_INDUCT, point_COMPONENTS);;
assert (length sv_thms = 2);;

(* Check orthogonality theorems (2 fields => 2 ordered pairs) *)
let orth_thms = record_orthogonality_thms (point_INDUCT, point_COMPONENTS);;
assert (length orth_thms = 2);;

(* Prove: writing xcoord updates it correctly *)
let XCOORD_READ_WRITE = prove
 (`!x s:test_point. read xcoord (write xcoord x s) = x`,
  GEN_TAC THEN MATCH_MP_TAC point_INDUCT THEN
  REWRITE_TAC[point_COMPONENTS]);;

(* Prove: writing xcoord leaves ycoord intact *)
let YCOORD_INTACT = prove
 (`!x s:test_point. read ycoord (write xcoord x s) = read ycoord s`,
  GEN_TAC THEN MATCH_MP_TAC point_INDUCT THEN
  REWRITE_TAC[point_COMPONENTS]);;

(* Test a record with 3 fields *)
let triple_INDUCT,triple_RECURSION,triple_COMPONENTS =
  define_auto_record_type
   "test_triple = { first: num; second: bool; third: num }";;

assert (length (get_record_components triple_COMPONENTS) = 3);;
assert (length (record_orthogonality_thms
                  (triple_INDUCT, triple_COMPONENTS)) = 6);;

(* ------------------------------------------------------------------------- *)
(* Test benign redefinition: defining the same record type twice must        *)
(* succeed and return the identical theorems from the cache, rather than     *)
(* failing with "new_basic_type_definition: Constant(s) already in use".     *)
(* ------------------------------------------------------------------------- *)

let point2_INDUCT,point2_RECURSION,point2_COMPONENTS =
  define_record_type "test_point = { xcoord: num; ycoord: num }";;

assert (concl point2_INDUCT = concl point_INDUCT);;
assert (concl point2_RECURSION = concl point_RECURSION);;
assert (concl point2_COMPONENTS = concl point_COMPONENTS);;

(* ------------------------------------------------------------------------- *)
(* Test that redefining a record type with different fields fails cleanly    *)
(* with the dedicated error message.                                         *)
(* ------------------------------------------------------------------------- *)

try
  let _ = define_record_type "test_point = { xcoord: bool; ycoord: num }" in
  assert false
with Failure msg ->
       assert (msg =
         "define_record_type: type test_point already defined with different fields")
   | Assert_failure _ as e -> raise e;;
