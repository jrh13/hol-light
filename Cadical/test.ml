(* ========================================================================= *)
(* Test the Cadical interface on a set of (relatively easy) tautologies.     *)
(* ========================================================================= *)

needs "Minisat/taut.ml";;

let TEST_TAUT TAUTCHECKER p =
  let th = time TAUTCHECKER p in
  if hyp th = [] && concl th = p
  then true else failwith "Wrong theorem";;

map (fun (p,s) -> print_string("Attempting "^s); print_newline();
                  s,TEST_TAUT CADICAL_PROVE p)
        all_taut;;
