(* ========================================================================= *)
(* 4CT/part2_compile.ml                                                      *)
(*                                                                           *)
(* Regenerating part2_compiled.hl, the evaluator OCaml code that             *)
(* eval_compile produces from the clause-fused rule database of              *)
(* part2_eval.ml (bytecode only: the generated file is loaded by `needs`,    *)
(* which native code cannot do; `make compiled` runs this file).  The        *)
(* generated file is an artifact, not a trust assumption: it only ever       *)
(* builds theorems through the kernel, so a wrong one fails or disagrees, it *)
(* cannot prove something false.                                             *)
(* ========================================================================= *)

needs "4CT/part2_eval.ml";;

let part2_compiled_fo3 = "4CT/part2_compiled.hl";;

let _ =
  let db = p1_build_db_fo3 (p1_contract_thms()) in
  let consts = dependencies db `check_reducible cf001` in
  write_rules_consts db ~margin:79 part2_compiled_fo3 consts;
  Printf.printf "=== part2_compile: %d evaluator groups written to %s ===\n%!"
    (length consts) part2_compiled_fo3;;
