(* ========================================================================= *)
(* 4CT/part2_final.ml                                                        *)
(*                                                                           *)
(* Part 2: the reducibility computation over the configurations (all 633, or *)
(* the range lo-hi given by FOURCOLOR_CONFIGS=lo-hi, for testing) by         *)
(* p2_run_indices (part2_run.ml), then REDUCIBILITY (the hypothesis          *)
(* reducibility of four_color.ml) by rewriting with the 633 results and the  *)
(* unconditional theorem FOUR_COLOR.  p2_final_thms is None unless all 633   *)
(* are present, and p2_final() returns REDUCIBILITY and FOUR_COLOR, or fails *)
(* if the run was restricted.  Loading this file on its own therefore proves *)
(* the hypermap theorem without the planar and map forms (and without        *)
(* Multivariate).                                                            *)
(* ========================================================================= *)

needs "4CT/four_color.ml";;
needs "4CT/part2_run.ml";;

let p2_indices =
  match (try Some (Sys.getenv "FOURCOLOR_CONFIGS") with Not_found -> None) with
    None -> 1 -- 633
  | Some s ->
      let i = try String.index s '-'
              with Not_found -> failwith "FOURCOLOR_CONFIGS must be lo-hi" in
      int_of_string (String.sub s 0 i) --
      int_of_string (String.sub s (i + 1) (String.length s - i - 1));;

p2_run_indices p2_indices;;

let p2_final_thms =
  if length !p2_results = 633 then begin
    let t0 = Sys.time() in
    let checks = map snd !p2_results in
    let REDUCIBILITY = prove(`reducibility`,
      REWRITE_TAC[reducibility; ALL_MEM; the_configs; ALL] THEN
      REWRITE_TAC checks) in
    let FOUR_COLOR = MP FOUR_COLOR_HYPERMAP REDUCIBILITY in
    Printf.printf "===REDUCIBILITY PROVED in %.1f s: %s===\n%!"
      (Sys.time() -. t0) (string_of_term (concl REDUCIBILITY));
    Printf.printf "===FOUR_COLOR: %s (hyps %d)===\n%!"
      (string_of_term (concl FOUR_COLOR)) (length (hyp FOUR_COLOR));
    Some (REDUCIBILITY, FOUR_COLOR)
  end else begin
    Printf.printf "===PART2_FINAL SKIPPED: %d of 633 results===\n%!"
      (length !p2_results); None
  end;;

let p2_final () =
  match p2_final_thms with
    Some thms -> thms
  | None -> failwith
 "FOURCOLOR_CONFIGS restricted the run, the theorems are not assembled";;
