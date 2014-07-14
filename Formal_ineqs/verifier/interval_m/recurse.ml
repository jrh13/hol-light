(* =========================================================== *)
(* OCaml verification procedure                                *)
(* Authors: Thomas C. Hales, Alexey Solovyev                   *)
(* Date: 2012-10-27                                            *)
(* =========================================================== *)

(* port of recurse.cc *)

(*
This is the code that verifies a disjunct of nonlinear inequalities.
The are given as a list   (tf:tfunction list).  If tf = [f1;....;fk], then
the list represents the inequality (f1 < 0 \/ f2 < 0 .... fk < 0).

The end user should only need to define a cell option,
and then call recursive_verifier, which recursively bisects the domain
until a partition of the domain is found on which verifier_cell gives
a pass on each piece of the partition.

*)

needs "verifier/interval_m/taylor.ml";;
needs "verifier/interval_m/report.ml";;
needs "verifier_options.hl";;

module Recurse = struct

open Interval_types;;
open Interval;;
open Univariate;;
open Line_interval;;
open Taylor;;
open Verifier_options;;
open List;;

type cellOption = {
  only_check_deriv1_negative : bool;
  is_using_dihmax : bool;
  is_using_bigface126 : bool;
  width_cutoff : float;
  allow_sharp : bool;
  allow_derivatives : bool;
  mutable iteration_count : int;
  iteration_limit : int;
  recursion_depth : int;
  mono_pass : bool;
  convex_flag : bool;
  raw_int_flag : bool;
  eps : float;
};;

(* cell verification is complex, and we use exceptions to
    exit as soon as the status has been determined.   *)

type mono_status = {
  variable : int;
  decr_flag : bool;
  df0_flag : bool;
  ti_flag : bool;
};;


type  cell_status =
  | Cell_pass of mono_status list list * bool
  | Cell_pass_mono of mono_status list list * mono_status
  | Cell_counterexample
  | Cell_inconclusive_ti of (mono_status list list * taylor_interval * float list * float list * float list * float list)
  | Cell_inconclusive of (mono_status list list * float list * float list * float list * float list);;

exception Return of cell_status;;

type result_tree =
  | Result_false of (float list * float list)
  | Result_pass of (bool * float list * float list)
  | Result_pass_mono of mono_status
  | Result_pass_ref of int
  | Result_mono of mono_status list * result_tree
      (* variable, convex_flag, r1, r2 *)
  | Result_glue of (int * bool * result_tree * result_tree);;

type p_status = {
        pp : int;
};;

type p_result_tree =
        | P_result_pass of p_status * bool
        | P_result_mono of p_status * mono_status list * p_result_tree
        | P_result_glue of p_status * int * bool * p_result_tree * p_result_tree
        | P_result_ref of int;;

let rec result_size r =
  match r with
    | Result_false _ -> failwith "False result detected"
    | Result_mono (_,r1) -> result_size r1
    | Result_glue (_, _, r1, r2) -> result_size r1 + result_size r2
    | Result_pass_mono _ -> 1
    | Result_pass _ -> 1
    | _ -> 0;;

let rec p_result_size r =
        match r with
                | P_result_pass _ -> 1
                | P_result_mono (_, _, r1) -> p_result_size r1
                | P_result_glue (_, _, _, r1, r2) -> p_result_size r1 + p_result_size r2
                | _ -> 0;;


let return c = raise (Return c);;


(* error checking and reporting functions *)

let string_of_domain x =
  let n = mth in
  Printf.sprintf "{%f, %f, %f, %f, %f, %f, %f, %f}" (n x 0) (n x 1) (n x 2) (n x 3) (n x 4) (n x 5) (n x 6) (n x 7);;

let string3 (x,z,s) =  (string_of_domain x ^"\n"^ string_of_domain z ^ "\n" ^ s);;

let boolify _ = true;;

let report_current = boolify o Report.report_timed o string3;;

let report_error = boolify o Report.report_error o string3;;

let report_fatal = boolify o Report.report_fatal o string3;;

(* let t = [0.1;0.2;0.3;0.4;0.5;0.6] in report_error (t,t,"ok");; *)

let periodic_count =
  let end_count = ref 0 in
    fun () ->
      let _ = end_count := !end_count + 1 in
        (0 = ( !end_count mod 1000));;

let check_limit opt depth =
  let _ = opt.iteration_count <- opt.iteration_count + 1 in
   ( opt.iteration_count < opt.iteration_limit or opt.iteration_limit = 0 ) &&
     (depth < opt.recursion_depth);;

let sgn x = if (x.lo > 0.0) then 1 else if (x.hi < 0.0) then -1 else 0;;

let rec same_sgn x y = (x = []) or (sgn (hd x) = sgn (hd y) && same_sgn (tl x) (tl y));;


(* has_monotone *)

let rec has_monotone opt tf ti domain0 x z x0 z0 is found = match is with
  | [] -> (x,z,x0,z0,List.rev found)
  | j::js when (mth x j >= mth z j) ->
      has_monotone opt tf ti domain0 x z x0 z0 js found
  | j::js ->
      let df_int =
        if opt.raw_int_flag then
          try evalf0 tf (j + 1) (fst domain0) (snd domain0)
          with Unstable -> mk_interval (-1.0,1.0)
        else
          mk_interval (-1.0, 1.0) in
      let allpos_df0, allpos_ti = df_int.lo >= opt.eps, lower_partial ti j >= opt.eps in
      let allneg_df0, allneg_ti = df_int.hi < ~-.(opt.eps), upper_partial ti j < ~-.(opt.eps) in
        if (allpos_df0 or allpos_ti) then
          let status =
            {variable = j + 1; decr_flag = false; df0_flag = allpos_df0; ti_flag = allpos_ti} in
            if opt.mono_pass && mth z j < mth z0 j then return (Cell_pass_mono ([], status))
            else
              let setj u = table (fun i -> (if i=j then mth z j else mth u i))  in
                has_monotone opt tf ti domain0 (setj x) (setj z)
                  (setj x0) (setj z0) js (status :: found)
        else if (allneg_df0 or allneg_ti) then
          let status =
            {variable = j + 1; decr_flag = true; df0_flag = allneg_df0; ti_flag = allneg_ti} in
            if opt.mono_pass && mth x j > mth x0 j then return (Cell_pass_mono ([], status))
            else
              let setj u = table (fun i -> (if i=j then mth x j else mth u i)) in
                has_monotone opt tf ti domain0 (setj x) (setj z)
                  (setj x0) (setj z0) js (status :: found)
        else has_monotone opt tf ti domain0 x z x0 z0 js found;;

(* loop as long as monotonicity keeps making progress.  *)

let rec going_strong(x,z,x0,z0,tf,opt,mono) =
  let (y,w) = center_form (x,z) in
  let maxwidth = maxl w in
  let target0 =
    if opt.raw_int_flag then
      try evalf0 tf 0 x z with Unstable -> one
    else
      one in
  let _ = target0.hi >= ~-.(opt.eps) or return (Cell_pass (mono, true)) in
  let target =
        try evalf tf x z with Unstable -> return (Cell_inconclusive (mono,x,z,x0,z0)) in
  let _ = upper_bound target >= ~-.(opt.eps) or return (Cell_pass (mono, false)) in
  let _ = lower_bound target < 0.0 or return Cell_counterexample in
  let epsilon_width = 1.0e-8 in
  let _ = (maxwidth >= epsilon_width) or return Cell_counterexample in
  let (x,z,x0,z0,strong) =
    if (opt.allow_derivatives) then
      try
        has_monotone opt tf target (x,z) x z x0 z0 iter8 []
      with Return (Cell_pass_mono (_, status)) -> return (Cell_pass_mono (mono, status))
    else (x,z,x0,z0,[]) in
    if (strong <> []) then
      going_strong(x,z,x0,z0,tf,opt,mono @ [strong])
    else
      (target,x,z,x0,z0,maxwidth,mono);;


(*
This procedure is mostly guided by heuristics that don't require formal
verification. In particular, no justification is required for tossing out inequalities
(since they appear as disjuncts, we can choose which one to prove).

Formal verification is required whenever a Cell_passes is issued,
and whenever the domain (x,z) is restricted.

The record (x0,z0) of the current outer boundary must be restricted to (x,z)
whenever an inequality is tossed out.
*)

let rec verify_cell (x,z,x0,z0,tf,opt) =
  try (
  let _ = not(periodic_count () && !info_print_level >= 2) or report_current (x,z,"periodic report") in
  let (ti,x,z,x0,z0,maxwidth,mono) = going_strong(x,z,x0,z0,tf,opt,[]) in
    if opt.convex_flag then
      Cell_inconclusive_ti (mono,ti,x,z,x0,z0)
    else
      Cell_inconclusive (mono,x,z,x0,z0)
  )
  with Return c -> c;;

let recursive_verifier (x,z,x0,z0,tf,opt) =
  let w_init, indices = unzip (filter (fun p -> fst p > 1e-8) (zip (map2 (-.) z x) (1--length x))) in
  let ws = map2 (-.) z x in
  let total_vol = itlist ( *. ) w_init 1.0 in
  let verified_vol = ref 0.0 in
  let last_report = ref 0 in
  let compute_vol x z w =
    let rec compute i indices x z w =
      match indices with
        | [] -> 1.0
        | (r :: t) when r = i ->
            let l = hd z -. hd x in
              (if l > 1e-8 then l else hd w) *. compute (i + 1) t (tl x) (tl z) (tl w)
        | _ -> compute (i + 1) indices (tl x) (tl z) (tl w) in
      compute 1 indices x z w in
  let update_verified_vol x z w =
    if !info_print_level > 0 then
      let _ = verified_vol := !verified_vol +. compute_vol x z w in
      let verified = int_of_float (!verified_vol /. total_vol *. 100.5) in
      if verified > !last_report then
        let _ = last_report := verified in report0 (sprintf "%d " !last_report) else ()
    else () in

  let rec rec_verifier (depth,x,z,x0,z0,w0,tf) =
    let _ = check_limit opt depth or report_fatal(x,z,Printf.sprintf "depth %d" depth) in
    let split_and_verify j x z x0 z0 convex_flag =
      let ( ++ ), ( / ) = up(); upadd, updiv in
      let yj = (mth x j ++  mth z j) / 2.0 in
      let delta b v = table (fun i-> if (i = j && b) then yj else mth v i) in
      let x1, z1 =
        if convex_flag then
          x, table (fun i -> if i = j then mth x i else mth z i)
        else
          delta false x, delta true z in
      let x2, z2 =
        if convex_flag then
          table (fun i -> if i = j then mth z i else mth x i), z
        else
          delta true x, delta false z in
      let w1 = table (fun i -> if i = j then mth w0 i / 2.0 else mth w0 i) in
      let r1 = rec_verifier(depth+1,x1,z1,x0,z0,w1,tf) in
        match r1 with
          | Result_false t -> Result_false t
          | _ ->
              (let r2 = rec_verifier(depth+1,x2,z2,x0,z0,w1,tf) in
                 match r2 with
                   | Result_false t -> Result_false t
                   | _ -> Result_glue (j, convex_flag, r1, r2)) in

    let add_mono mono r1 =
      itlist (fun m r -> Result_mono (m, r)) mono r1 in

      match verify_cell(x,z,x0,z0,tf,opt)  with
        | Cell_counterexample -> Result_false (x,z)
        | Cell_pass (mono, f0_flag) ->
            let _ = update_verified_vol x z w0 in
              add_mono mono (Result_pass (f0_flag,x,z))
        | Cell_pass_mono (mono, status) ->
            let _ = update_verified_vol x z w0 in
              add_mono mono (Result_pass_mono status)
        | Cell_inconclusive_ti(mono,ti,x,z,x0,z0) ->
            let dds = map (fun i -> mth (mth ti.dd i) i, i) iter8 in
            let convex_dds = filter (fun dd, i -> dd.lo >= opt.eps && mth x i < mth z i) dds in
            let convex_i = map snd convex_dds in
            let w2 = List.map2 upsub z x in
            let convex_flag, ws, ws_i =
              if convex_dds = [] then
                false, w2, iter8
              else
                true, map (mth w2) convex_i, convex_i in
            let maxwidth2 = maxl ws in
            let j_wide =  try( find (fun i -> mth w2 i = maxwidth2) ws_i) with
              | _ -> failwith "recursive_verifier find" in
              add_mono mono (split_and_verify j_wide x z x0 z0 convex_flag)

        | Cell_inconclusive(mono,x,z,x0,z0) ->
            let w2 = List.map2 upsub z x in
            let maxwidth2 = maxl w2 in
            let j_wide =  try( find (fun i -> mth w2 i = maxwidth2) iter8) with
              | _ -> failwith "recursive_verifier find" in
              add_mono mono (split_and_verify j_wide x z x0 z0 false) in

    rec_verifier (0,x,z,x0,z0,ws,tf);;



 end;;
