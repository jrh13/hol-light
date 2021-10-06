
(* ------------------------------------------------------------------ *)
(* This bundles an interactive session into a proof. *)
(* ------------------------------------------------------------------ *)

let labels_flag = ref false;;


let LABEL_ALL_TAC:tactic =
 let mk_label avoid =
  let rec mk_one_label i avoid  =
    let label = "Z-"^(string_of_int i) in
      if not(mem label avoid) then label else mk_one_label (i+1) avoid in
    mk_one_label 0 avoid in
 let update_label i asl =
  let rec f_at_i f j =
    function [] -> []
      | a::b -> if (j=0) then (f a)::b else a::(f_at_i f (j-1) b) in
  let avoid = map fst asl in
  let current = el i avoid in
  let new_label = mk_label avoid in
  if (String.length current > 0) then asl else
    f_at_i (fun (_,y) -> (new_label,y) ) i asl in
  fun (asl,w) ->
    let aslp = ref asl in
    (for i=0 to ((length asl)-1) do (aslp := update_label i !aslp) done;
    (ALL_TAC (!aslp,w)));;

(* global_var *)
let (EVERY_STEP_TAC:tactic ref) = ref ALL_TAC;;

let (e:tactic ->goalstack) =
   fun tac -> refine(by(VALID
   (if !labels_flag then (tac THEN (!EVERY_STEP_TAC)) THEN LABEL_ALL_TAC
   else tac)));;

let has_stv t =
  let typ = (type_vars_in_term t) in
  can (find (fun ty -> (is_vartype ty) && ((dest_vartype ty).[0] = '?'))) typ;;

let prove_by_refinement(t,(tacl:tactic list)) =
  if (length (frees t) > 0)
    then failwith "prove_by_refinement: free vars" else
  if (has_stv t)
    then failwith "prove_by_refinement: has stv" else
  let gstate = mk_goalstate ([],t) in
  let _,sgs,just = rev_itlist
    (fun tac gs -> by
       (if !labels_flag then (tac THEN
         (!EVERY_STEP_TAC) THEN LABEL_ALL_TAC ) else tac) gs)
     tacl gstate in
  let th = if sgs = [] then just null_inst []
  else failwith "BY_REFINEMENT_PROOF: Unsolved goals" in
  let t' = concl th in
  if t' = t then th else
  try EQ_MP (ALPHA t' t) th
  with Failure _ -> failwith "prove_by_refinement: generated wrong theorem";;


(* ------------------------------------------------------------------ *)
(* DUMPING AND PRELOADED THEOREMS *)
(* ------------------------------------------------------------------ *)


let saved_thm = ref ((Hashtbl.create 300):(term,thm) Hashtbl.t);;
let save_thm thm = Hashtbl.add !saved_thm (concl thm) thm;;
let mem_thm tm = Hashtbl.mem !saved_thm tm;;
let remove_thm tm = Hashtbl.remove !saved_thm tm;;
let find_thm tm = Hashtbl.find !saved_thm tm;;

let dump_thm file_name =
    let ch = open_out_bin file_name in
    (output_value ch !saved_thm;
    close_out ch);;

let load_thm file_name =
  let ch = open_in_bin file_name in
  (saved_thm := input_value ch;
   close_in ch);;

(* ------------------------------------------------------------------ *)
(* PROOFS STORED.  *)
(* ------------------------------------------------------------------ *)

let old_prove = prove;;
let old_prove_by_refinement = prove_by_refinement;;
let fast_load  = ref true;;

let set_fast_load file_name =
  (fast_load := true;
  load_thm file_name);;

let set_slow_load () =
  (fast_load := false;);;

let prove (x, tac) =
  if (!fast_load) then (try(find_thm x) with failure -> old_prove(x,tac))
  else (let t = old_prove(x,tac) in (save_thm t; t));;

let prove_by_refinement (x, tacl) =
  if (!fast_load) then (try(find_thm x)
			with failure -> old_prove_by_refinement(x,tacl))
  else (let t = old_prove_by_refinement(x,tacl) in (save_thm t; t));;

if (false) then (set_fast_load "thm.dump") else (fast_load:=false);;

