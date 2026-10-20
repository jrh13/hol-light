(* ========================================================================= *)
(* 4CT/par_hook.ml                                                           *)
(*                                                                           *)
(* The switch between sequential and parallel evaluation of the independent  *)
(* computations: the side conditions of the presentation scripts             *)
(* (present_eval.ml) and the 633 configurations of Part 2 (part2_run.ml).    *)
(* This file is plain OCaml 4.03.  By default par_enabled is false and       *)
(* everything runs sequentially, exactly as without this file.  parallel.ml  *)
(* (OCaml 5 or later), loaded before make.ml by make_parallel.ml, installs   *)
(* a par_mapper running the jobs in OCaml domains and sets par_enabled.      *)
(*                                                                           *)
(*   (!par_mapper).par_map n f jobs   Some(f d x) for each job x, run in     *)
(*                                    domain d (0 here), or None if f        *)
(*                                    failed; up to n domains                *)
(*   !par_say f                       run the printing function f (under a   *)
(*                                    lock when parallel)                    *)
(*   !par_time ()                     seconds, for timings (wall clock when  *)
(*                                    parallel, Sys.time here)               *)
(* ========================================================================= *)

type par_mapper =
  { par_map :
      'a 'b. int -> (int -> 'a -> 'b) -> 'a array -> 'b option array };;

let par_enabled = ref false;;

let par_domains = ref 1;;

let par_mapper =
  ref { par_map = fun _ f jobs ->
          Array.map (fun x -> try Some(f 0 x) with Failure _ -> None) jobs };;

let par_say = ref (fun (f:unit->unit) -> f());;

let par_time = ref Sys.time;;
