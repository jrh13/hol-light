(* =========================================================== *)
(* OCaml verification and result transformation functions      *)
(* Author: Alexey Solovyev                                     *)
(* Date: 2012-10-27                                            *)
(* =========================================================== *)

needs "verifier/interval_m/recurse.ml";;
needs "verifier/interval_m/recurse0.ml";;

module Verifier = struct

open Interval_types;;
open Interval;;
open Univariate;;
open Line_interval;;
open Taylor;;
open Recurse;;


type certificate_stats =
{
  pass : int;
  pass_raw : int;
  pass_mono : int;
  mono : int;
  glue : int;
  glue_convex : int;
};;


let dummy_stats =
{
  pass = 0; pass_raw = 0; pass_mono = 0;
  mono = 0; glue = 0; glue_convex = 0;
};;


(**********************************)
let run_test f x z min_flag min_max allow_d convex_flag mono_pass_flag raw_int_flag eps =
  let pad = replicate 0.0 (8 - length x) in
  let xx = x @ pad and zz = z @ pad in
  let mone = mk_interval(-1.0,-1.0) in
  let neg_f = Scale(f, mone) in
  let ff = if min_flag then
    Plus(neg_f, Scale(unit,mk_interval(min_max, min_max)))
  else
    Plus(f, Scale(unit, ineg (mk_interval(min_max, min_max)))) in
  let opt =  {
    only_check_deriv1_negative = false;
    is_using_dihmax =false;
    is_using_bigface126 =false;
    width_cutoff =0.05;
    allow_sharp =false;
    allow_derivatives =allow_d;
    iteration_count =0;
    iteration_limit =0;
    recursion_depth =200;
    mono_pass = mono_pass_flag;
    convex_flag = convex_flag;
    raw_int_flag = raw_int_flag;
    eps = eps;
  } in
    recursive_verifier(xx,zz,xx,zz,ff,opt);;


(* A verification procedure which uses raw interval arithmetic only *)
(*
open Recurse0;;

let run_test0 f x z min_flag min_max allow_d convex_flag mono_pass_flag eps =
  let pad = replicate 0.0 (8 - length x) in
  let xx = x @ pad and zz = z @ pad in
  let mone = mk_interval(-1.0,-1.0) in
  let neg_f = Scale(f, mone) in
  let ff = if min_flag then
    Plus(neg_f, Scale(unit,mk_interval(min_max, min_max)))
  else
    Plus(f, Scale(unit, ineg (mk_interval(min_max, min_max)))) in
  let opt =  {
    only_check_deriv1_negative = false;
    is_using_dihmax =false;
    is_using_bigface126 =false;
    width_cutoff =0.05;
    allow_sharp =false;
    allow_derivatives =allow_d;
    iteration_count =0;
    iteration_limit =0;
    recursion_depth =200;
    mono_pass = mono_pass_flag;
    convex_flag = convex_flag;
    raw_int_flag = true;
    eps = eps;
  } in
    recursive_verifier0(0,xx,zz,xx,zz,ff,opt);;
*)


(****************************************)

let domain_str x z =
  let s1 = map string_of_float x and
      s2 = map string_of_float z in
    sprintf "[%s], [%s]" (String.concat "; " s1) (String.concat "; " s2);;

let path_str p =
  String.concat "," (map (fun s, j -> sprintf "%s(%d)" s j) p);;


(* get_results0 *)
(* This function finds all subtrees of the given solution tree which can be
   veified immediately (no Result_pass_mono). These subtrees are added to
   the accumulator. Paths to the roots of all subtrees are also saved in
   the accumulator. The third returned value is a solution tree where all
   found subtrees are replaced with Result_pass_ref j, with j = #of the corresponding
   subtree in the accumulator (1-based) *)


let get_results0 path r acc =
  let dummy_tree = Result_false ([], []) in
  let is_ref r = match r with Result_pass_ref _ -> true | _ -> false in

  let rec get_rec path r acc =
    match r with
      | Result_mono (mono, r1) ->
          let get_m m = (if m.decr_flag then "ml" else "mr"), m.variable in
          let path' = rev_itlist (fun m l -> get_m m :: l) mono path in
          let flag, acc', tree = get_rec path' r1 acc in
            if flag then true, acc', dummy_tree
            else false, acc', Result_mono (mono, tree)
      | Result_glue (j, convex_flag, r1, r2) ->
          let s1, s2 = if convex_flag then "ml", "mr" else "l", "r" in
          let p1, p2 = ((s1, j + 1) :: path), ((s2, j + 1) :: path) in
          let flag1, acc1, tree1 = get_rec p1 r1 acc in
          let flag2, acc', tree2 = get_rec p2 r2 acc1 in
          let n = (length acc' + 1) in
            if flag1 then
              if flag2 then
                true, acc', dummy_tree
              else if is_ref r1 then
                false, acc', Result_glue (j, convex_flag, r1, tree2)
              else
                false, acc' @ [rev p1, r1], Result_glue (j, convex_flag, Result_pass_ref n, tree2)
            else
              if flag2 then
                if is_ref r2 then
                  false, acc', Result_glue (j, convex_flag, tree1, r2)
                else
                  false, acc' @ [rev p2, r2], Result_glue (j, convex_flag, tree1, Result_pass_ref n)
              else
                false, acc', Result_glue (j, convex_flag, tree1, tree2)

      | Result_pass_mono _ -> false, acc, r
      | _ -> true, acc, dummy_tree in

    get_rec path r acc;;




(* transform_result *)


let transform_result x z r =
  (* get_domain *)
  (* Subdivides the given domain (x,z) according to the given path *)
  let domain_hash = Hashtbl.create 1000 in
  let find_hash, mem_hash, add_hash =
    Hashtbl.find domain_hash, Hashtbl.mem domain_hash, Hashtbl.add domain_hash in

  let get_domain path =
    let n = length x in
    let table f = map f (0--(n - 1)) in
    let rec rec_domain (x, z) path hash =
      match path with
        | [] -> x, z
        | (s, j) :: ps ->
            let hash' = hash^s^(string_of_int j) in
              if mem_hash hash' then
                rec_domain (find_hash hash') ps hash'
              else
                let j = j - 1 in
                let domain' =
                  if s = "l" or s = "r" then
                    let ( ++ ), ( / ) = up(); upadd, updiv in
                    let yj = (mth x j ++ mth z j) / 2.0 in
                    let delta b v = table (fun i -> if i = j && b then yj else mth v i) in
                      if s = "l" then
                        delta false x, delta true z
                      else
                        delta true x, delta false z
                  else
                    if s = "ml" then
                      x, table (fun i -> if i = j then mth x i else mth z i)
                    else
                      table (fun i -> if i = j then mth z i else mth x i), z in
                let _ = add_hash hash' domain' in
                  rec_domain domain' ps hash' in
      rec_domain (x,z) path "" in

  (* sub_domain *)
  (* Verifies if interval [x',z'] SUBSET interval [x,z] *)
  let sub_domain (x',z') (x,z) =
    let le a b = itlist2 (fun a b c -> c & (a <= b)) a b true in
      le x x' & le z' z in

  (* transform_pass_mono *)
  (* Replaces all (Result_pass_mono m) with (Result_mono [m] (Result_ref j)) where
     j is the reference to the corresponding domain *)
  let transform_pass_mono x z domains r =
    let domains_i = zip domains (1--length domains) in

    let find_domain x' z' =
      try find (fun d, _ -> sub_domain (x', z') d) domains_i with Failure _ -> (x,z), -1 in

    let get_m m = (if m.decr_flag then "ml" else "mr"), m.variable in

    let rec rec_transform path r =
      match r with
        | Result_mono (mono, r1) ->
            let path' = rev_itlist (fun m l -> get_m m :: l) mono path in
              Result_mono (mono, rec_transform path' r1)
        | Result_glue (j, convex_flag, r1, r2) ->
            let s1, s2 = if convex_flag then "ml", "mr" else "l", "r" in
            let p1, p2 = ((s1, j + 1) :: path), ((s2, j + 1) :: path) in
            let t1 = rec_transform p1 r1 in
            let t2 = rec_transform p2 r2 in
              Result_glue (j, convex_flag, t1, t2)
        | Result_pass_mono m ->
            let path' = rev (get_m m :: path) in
            let x', z' = get_domain path' in
            let _, i = find_domain x' z' in
              (*          let _ = report (sprintf "p = %s, d = %s, found: %d"
                          (domain_str x' z') (path_str path') i) in *)
              if i >= 0 then Result_mono ([m], Result_pass_ref (-i)) else r
        | _ -> r in

      rec_transform [] r in

  let rec transform acc r =
    let flag, rs, r' = get_results0 [] r acc in
      if flag then (rs @ [[], r])
      else
        let domains = map (fun p, _ -> get_domain p) rs in
        let r_next = transform_pass_mono x z domains r' in
        let _ = r_next <> r' or failwith "transform_result: deadlock" in
          transform rs r_next in
    transform [] r;;


(* Computes result statistics *)

let result_stats result =
  let pass = ref 0 and
      mono = ref 0 and
      glue = ref 0 and
      pass_mono = ref 0 and
      pass_raw = ref 0 and
      glue_convex = ref 0 in

  let rec count r =
    match r with
      | Result_false _ -> failwith "False result"
      | Result_pass (flag, _, _) ->
          pass := !pass + 1;
          if flag then pass_raw := !pass_raw + 1 else ()
      | Result_pass_mono _ -> pass_mono := !pass_mono + 1
      | Result_mono (_, r1) -> mono := !mono + 1; count r1
      | Result_glue (_, flag, r1, r2) ->
          glue := !glue + 1;
          if flag then glue_convex := !glue_convex + 1 else ();
          count r1; count r2 in

  let _ = count result in
    {pass = !pass; pass_raw = !pass_raw; pass_mono = !pass_mono;
     mono = !mono; glue = !glue; glue_convex = !glue_convex};;


let report_stats stats =
  let s = sprintf "pass = %d (pass_raw = %d)\nmono = %d\nglue = %d (glue_convex = %d)\npass_mono = %d"
    stats.pass stats.pass_raw stats.mono stats.glue stats.glue_convex stats.pass_mono in
    report s;;


let result_p_stats glue_flag p_result =
  let p_table = Hashtbl.create 10 in
  let add1 p =
    let c = if Hashtbl.mem p_table p then Hashtbl.find p_table p else 0 in
      Hashtbl.replace p_table p (succ c) in

  let rec count r =
    match r with
      | P_result_ref _ -> ()
      | P_result_pass (pp, _) -> add1 pp.pp
      | P_result_mono (pp, _, r1) -> add1 pp.pp; count r1
      | P_result_glue (pp, _, _, r1, r2) ->
          if glue_flag then add1 pp.pp else ();
          count r1; count r2 in

  let _ = count p_result in
  let s = Hashtbl.fold
    (fun p c s -> (sprintf "p = %d: %d\n" p c) ^ s) p_table "" in
    report s;;


end;;
