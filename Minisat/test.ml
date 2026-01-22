(* ========================================================================= *)
(* Try both Minisat and zchaff on a set of tautologies.                      *)
(* ========================================================================= *)

needs "Minisat/taut.ml";;

let TEST_TAUT TAUTCHECKER p =
  try let th = time TAUTCHECKER p in
      if hyp th = [] && concl th = p
      then true else failwith "Wrong theorem"
  with Sat_counterexample th ->
      if rand(rand(concl th)) = p then false
      else failwith "Wrong counterexample";;

map (fun (p,s) -> print_string("Attempting "^s); print_newline();
                  s,TEST_TAUT SAT_PROVE p,TEST_TAUT ZSAT_PROVE p)
        all_taut;;
