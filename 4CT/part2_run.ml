(* ========================================================================= *)
(* 4CT/part2_run.ml                                                          *)
(*                                                                           *)
(* Part 2: running the compiled check_reducible evaluator (f_check_reducible *)
(* of part2_compiled.hl, on part2_eval.ml) over the configurations;          *)
(* p2_run_indices records the theorems |- check_reducible cfNNN <=> T in     *)
(* p2_results.  With parallel.ml loaded (OCaml 5, par_hook.ml) the           *)
(* configurations run in !par_domains domains (p2_run_parallel), with the    *)
(* same theorems recorded in the same order.                                 *)
(* ========================================================================= *)

needs "4CT/part2_eval.ml";;
needs "4CT/part2_compiled.hl";;
needs "4CT/part2_config_list.ml";;
needs "4CT/cfreducible.ml";;
needs "4CT/par_hook.ml";;
needs "4CT/part2_cost_order.ml";;

let p2_results = ref ([] : (int * thm) list);;

let p2_run_sequential idxs =
  let total = ref 0.0 in
  List.iter (fun i ->
    let cf_thm = assoc i p2_config_thms in
    let t0 = Sys.time() in
    let th = f_check_reducible (rand (concl cf_thm))
      (Some (AP_TERM `check_reducible` cf_thm)) in
    let dt = Sys.time() -. t0 in
    total := !total +. dt;
    p2_results := (i, th) :: !p2_results;
    Printf.printf "P2: cf%03d %s in %.2f s (total %.1f s)\n%!" i
      (string_of_term (rand (concl th))) dt !total)
    idxs;
  Printf.printf "===P2_RUN_DONE: %d configs, %.1f s===\n%!"
    (length idxs) !total;;

(* ------------------------------------------------------------------------- *)
(* The parallel mode.  The evaluator calls only the kernel rules, the        *)
(* numeral conversions of calc_num.ml and cprsize_conv (SIMP_CONV, which     *)
(* only reads the global simpset): it never parses, prints or caches, and    *)
(* the jobs share nothing mutable.  The input theorems |- check_reducible    *)
(* cfNNN = check_reducible (...) are built before the domains start, the     *)
(* heaviest configurations (p2_cost_order) first, and the results are        *)
(* printed under par_say.                                                    *)
(* ------------------------------------------------------------------------- *)

(* The ring size of configuration i (cprsize: 2, plus 1 per CpY and 2 per    *)
(* CpU).                                                                     *)
let p2_ring_size i =
  let prog = fst(dest_pair(rand(concl(assoc i p2_config_thms)))) in
  itlist (fun s n -> match s with
                       Const("CpY",_) -> n + 1
                     | Const("CpU",_) -> n + 2
                     | _ -> n) (dest_list prog) 2;;

let p2_run_parallel idxs =
  let ndomains = !par_domains and ckr = `check_reducible` in
  let rank i = try index i p2_cost_order
               with Failure _ -> length p2_cost_order in
  let bigger (k,i) (k',i') =
    let c = rank i and c' = rank i' in
    let r = p2_ring_size i and r' = p2_ring_size i' in
    c < c' || c = c' && (r > r' || r = r' && k < k') in
  let jobs = Array.of_list
   (map (fun (k,i) -> let cf_thm = assoc i p2_config_thms in
                      k,i,rand(concl cf_thm),AP_TERM ckr cf_thm)
        (sort bigger (zip (0--(length idxs - 1)) idxs))) in
  let n = Array.length jobs and ndone = ref 0 in
  let t0 = !par_time() and c0 = Sys.time() in
  let check d (k,i,tm,th0) =
    let t1 = !par_time() in
    let th = try f_check_reducible tm (Some th0) with e ->
      (!par_say (fun () -> Printf.printf "P2: cf%03d FAILED\n%!" i);
       raise e) in
    let t2 = !par_time() in
    !par_say (fun () ->
      incr ndone;
      Printf.printf "P2: cf%03d %s in %.2f s (domain %d, %d/%d, %.1f s)\n%!"
        i (string_of_term(rand(concl th))) (t2 -. t1) d !ndone n (t2 -. t0));
    k,i,th,t2 -. t1 in
  Printf.printf "===P2_PARALLEL: %d configs, %d domains===\n%!"
    n (max 1 (min ndomains n));
  let res = Array.to_list ((!par_mapper).par_map ndomains check jobs) in
  let wall = !par_time() -. t0 and cpu = Sys.time() -. c0 in
  let good = sort (fun (k,_,_,_) (k',_,_,_) -> k < k')
                  (mapfilter (function Some r -> r | None -> fail()) res) in
  let busy = itlist (fun (_,_,_,dt) s -> s +. dt) good 0.0 in
  let ok = filter (fun (_,_,th,_) -> hyp th = [] && rand(concl th) = `T`)
                  good in
  p2_results := rev_itlist (fun (_,i,th,_) l -> (i,th)::l) good !p2_results;
  Printf.printf "===P2_PARALLEL_DONE: %d configs in %d domains, %d T with \
                 no hypotheses, %d failed; wall %.1f s, CPU %.1f s, busy \
                 %.1f s===\n%!"
    n (max 1 (min ndomains n)) (length ok) (n - length good) wall cpu busy;
  if length good < n then
    failwith "p2_run_parallel: some configurations failed";;

let p2_run_indices idxs =
  if !par_enabled then p2_run_parallel idxs else p2_run_sequential idxs;;
