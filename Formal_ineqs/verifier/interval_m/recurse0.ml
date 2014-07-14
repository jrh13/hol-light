(* ============================================================= *)
(* OCaml verification procedure (basic interval arithmetic only) *)
(* Authors: Thomas C. Hales, Alexey Solovyev                     *)
(* Date: 2012-10-27                                              *)
(* ============================================================= *)

(* Recursive verification of inequalities using the basic interval arithmetic only *)

needs "verifier/interval_m/recurse.ml";;

module Recurse0 = struct

open Interval_types;;
open Interval;;
open Univariate;;
open Line_interval;;
open Taylor;;
open Recurse;;



(* has_monotone *)

let rec has_monotone0 opt tf domain0 x z x0 z0 is found = match is with
  | [] -> (x,z,x0,z0,List.rev found)
  | j::js when (mth x j >= mth z j) ->
      has_monotone0 opt tf domain0 x z x0 z0 js found
  | j::js ->
      let df_int = try evalf0 tf (j + 1) (fst domain0) (snd domain0) with Unstable -> mk_interval (-1.0,1.0) in
      let allpos_df0 = df_int.lo >= opt.eps in
      let allneg_df0 = df_int.hi < ~-.(opt.eps) in
        if allpos_df0 then
          let status =
            {variable = j + 1; decr_flag = false; df0_flag = allpos_df0; ti_flag = false} in
            if opt.mono_pass && mth z j < mth z0 j then return (Cell_pass_mono ([], status))
            else
              let setj u = table (fun i -> (if i=j then mth z j else mth u i))  in
                has_monotone0 opt tf domain0 (setj x) (setj z)
                  (setj x0) (setj z0) js (status :: found)
        else if allneg_df0 then
          let status =
            {variable = j + 1; decr_flag = true; df0_flag = allneg_df0; ti_flag = false} in
            if opt.mono_pass && mth x j > mth x0 j then return (Cell_pass_mono ([], status))
            else
              let setj u = table (fun i -> (if i=j then mth x j else mth u i)) in
                has_monotone0 opt tf domain0 (setj x) (setj z)
                  (setj x0) (setj z0) js (status :: found)
        else has_monotone0 opt tf domain0 x z x0 z0 js found;;

(* loop as long as monotonicity keeps making progress.  *)

let rec going_strong0(x,z,x0,z0,tf,opt,mono) =
  let (y,w) = center_form (x,z) in
  let maxwidth = maxl w in
  let target0 = try evalf0 tf 0 x z with Unstable -> return (Cell_inconclusive (mono,x,z,x0,z0)) in
  let _ = target0.hi >= ~-.(opt.eps) or return (Cell_pass (mono, true)) in
  let epsilon_width = 1.0e-8 in
  let _ = (maxwidth >= epsilon_width) or return Cell_counterexample in
  let (x,z,x0,z0,strong) =
    if (opt.allow_derivatives) then
      try
        has_monotone0 opt tf (x,z) x z x0 z0 iter8 []
      with Return (Cell_pass_mono (_, status)) -> return (Cell_pass_mono (mono, status))
    else (x,z,x0,z0,[]) in
    if (strong <> []) then
      going_strong0(x,z,x0,z0,tf,opt,mono @ [strong])
    else
      (x,z,x0,z0,maxwidth,mono);;


(*
This procedure is mostly guided by heuristics that don't require formal
verification. In particular, no justification is required for tossing out inequalities
(since they appear as disjuncts, we can choose which one to prove).

Formal verification is required whenever a Cell_passes is issued,
and whenever the domain (x,z) is restricted.

The record (x0,z0) of the current outer boundary must be restricted to (x,z)
whenever an inequality is tossed out.
*)

let rec verify_cell0 (x,z,x0,z0,tf,opt) =
  try (
    let _ = not(periodic_count ()) or report_current (x,z,"periodic report") in
    let (x,z,x0,z0,maxwidth,mono) = going_strong0(x,z,x0,z0,tf,opt,[]) in
      if opt.convex_flag then
        let ti = try evalf tf x z with Unstable -> return (Cell_inconclusive (mono,x,z,x0,z0)) in
          Cell_inconclusive_ti (mono,ti,x,z,x0,z0)
      else
        Cell_inconclusive (mono,x,z,x0,z0)
  )
  with Return c -> c;;

let rec recursive_verifier0 (depth,x,z,x0,z0,tf,opt) =
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
    let r1 = recursive_verifier0(depth+1,x1,z1,x0,z0,tf,opt) in
      match r1 with
        | Result_false t -> Result_false t
        | _ ->
            (let r2 = recursive_verifier0(depth+1,x2,z2,x0,z0,tf,opt) in
               match r2 with
                 | Result_false t -> Result_false t
                 | _ -> Result_glue (j, convex_flag, r1, r2)) in

  let add_mono mono r1 =
    itlist (fun m r -> Result_mono (m, r)) mono r1 in


    match verify_cell0(x,z,x0,z0,tf,opt)  with
      | Cell_counterexample -> Result_false (x,z)
      | Cell_pass (mono, f0_flag) -> add_mono mono (Result_pass (f0_flag,x,z))
      | Cell_pass_mono (mono, status) -> add_mono mono (Result_pass_mono status)
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
            add_mono mono (split_and_verify j_wide x z x0 z0 false);;



 end;;
