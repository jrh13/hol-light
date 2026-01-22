(* This file must be loaded inside HOL Light proof files *)

unset_jrh_lexer;;
module ExportTrace = struct
  type tac_record = {
    definition_line_number: string * int;
    user_line_number: string * int;
    goal_before: goal;
    goals_after: goal list;
    num_subgoals: int;
  }

  type conv_record = {
    definition_line_number: string * int;
    user_line_number: string * int;
    input: term;
    output: thm
  }

  (* Separate record_args to lazily evaluate this (otherwise it takes too long) *)
  type record_args = {
    names: string list;
    types: string list;
    values: string list;
    exprs: string list;
  }

  (***************************************************************************)
  (*        For sorting and pruning too large or uninteresting cases         *)
  (***************************************************************************)

  let is_term_too_large (t:term): bool =
    let maxcnt = 1000 in
    let rec fn (t:term): int =
      if is_numeral t then 1 else
      match t with
      | Comb(x,y) ->
        let cx = fn(x) in
        if cx > maxcnt then cx
        else cx + fn(y)
      | Const _ -> 1
      | Var _ -> 1
      | Abs(_,y) -> 1 + fn(y)
    in fn(t) > maxcnt

  (** For tactics **)

  (* # records to keep in tac_locs *)
  let max_num_records = 20

  let is_goal_too_large (a_goal:goal): bool =
    (* Max. assumptions that a goal may have; otherwise drop it *)
    let max_assumptions = 150 in
    let asl,w = a_goal in
    List.length asl > max_assumptions ||
    is_term_too_large w

  type tac_record_interestingness = {
    (* The length of string_of concl of goal_before. Shorter is better *)
    input_concl_str_len: int
  }
  let mk_tac_record_interestingness (tr:tac_record) =
    {
      input_concl_str_len = String.length (string_of_term (snd tr.goal_before))
    }

  let all_tac_records_interesting
      (tr: (tac_record * record_args * tac_record_interestingness) list): bool =
    let interesting_concl_strlen = 100 in
    List.for_all (fun (_,_,i) -> i.input_concl_str_len < interesting_concl_strlen)
      tr

  let compare_tac_interestingness
      (r1:tac_record_interestingness) r2: int =
    (* Just compare the size of the input conclusion *)
    compare r1.input_concl_str_len r2.input_concl_str_len


  (** For conversions **)

  type conv_record_interestingness = {
    (* The length of string_of_term of input. Shorter is better *)
    input_term_str_len: int
  }
  let mk_conv_record_interestingness (cr:conv_record) =
    {
      input_term_str_len = String.length (string_of_term cr.input)
    }

  let all_conv_records_interesting
      (tr: (conv_record * record_args * conv_record_interestingness) list): bool =
    let interesting_term_strlen = 50 in
    List.for_all (fun (_,_,i) -> i.input_term_str_len < interesting_term_strlen)
      tr

  let compare_conv_interestingness
      (r1:conv_record_interestingness) r2: int =
    (* Just compare the size of the input terms *)
    compare r1.input_term_str_len r2.input_term_str_len


  (***************************************************************************)
  (*                                  Full record                            *)
  (***************************************************************************)

  let tac_logs
    :(string,
        (tac_record * record_args * tac_record_interestingness) list)
      Hashtbl.t =
    Hashtbl.create 128
  let conv_logs
    :(string,
        (conv_record * record_args * conv_record_interestingness) list)
      Hashtbl.t =
    Hashtbl.create 128


end;;


let exptrace_add_tac (tactic_name:string)
        (re:ExportTrace.tac_record)
        (re_arg_gen:unit -> ExportTrace.record_args)=
  if ExportTrace.is_goal_too_large re.goal_before ||
    List.exists ExportTrace.is_goal_too_large re.goals_after
  then () (* too large goal to register :( *) else

  let logs = ExportTrace.tac_logs in
  (* Lazily calculate interestingness of this tac_record 're'. *)
  let mk_i () = ExportTrace.mk_tac_record_interestingness re in

  let mk_full_rec() = (re, re_arg_gen(), mk_i()) in

  match Hashtbl.find_opt logs tactic_name with
  | None ->
    Hashtbl.add logs tactic_name [mk_full_rec()]
  | Some records ->
    if List.length records < ExportTrace.max_num_records then
      Hashtbl.replace logs tactic_name (mk_full_rec()::records)
    else if ExportTrace.all_tac_records_interesting records then
      () (* no need to update records *)
    else begin
      assert (List.length records = ExportTrace.max_num_records);
      let new_records = List.sort
          (fun (_,_,i1) (_,_,i2) -> ExportTrace.compare_tac_interestingness i1 i2)
          (mk_full_rec()::records) in
      let new_records = rev (tl (rev new_records)) in
      Hashtbl.replace logs tactic_name new_records
    end;;

let exptrace_add_conv (conv_name:string)
        (re:ExportTrace.conv_record)
        (re_arg_gen:unit -> ExportTrace.record_args) =
  (* If the input term is too large, skip this *)
  if ExportTrace.is_term_too_large re.input then () else
  (* If the result is 't = t', ignore this *)
  if let c = concl re.output in is_eq c && lhs c = rhs c
  then () (* not interesting! *) else

  let logs = ExportTrace.conv_logs in
  (* Lazily calculate interestingness of this tac_record 're'. *)
  let mk_i () = ExportTrace.mk_conv_record_interestingness re in

  let mk_full_rec() = (re, re_arg_gen(), mk_i()) in

  match Hashtbl.find_opt logs conv_name with
  | None ->
    Hashtbl.add logs conv_name [mk_full_rec()]
  | Some records ->
    if List.length records < ExportTrace.max_num_records then
      Hashtbl.replace logs conv_name (mk_full_rec()::records)
    else if ExportTrace.all_conv_records_interesting records then
      () (* no need to update records *)
    else begin
      assert (List.length records = ExportTrace.max_num_records);
      let new_records = List.sort
          (fun (_,_,i1) (_,_,i2) -> ExportTrace.compare_conv_interestingness i1 i2)
          (mk_full_rec()::records) in
      let new_records = rev (tl (rev new_records)) in
      Hashtbl.replace logs conv_name new_records
    end;;

let exptrace_dump (dir_path:string): unit =
  let tac_logs = ExportTrace.tac_logs in
  let tac_rec_comp (_,_,i1) (_,_,i2) = ExportTrace.compare_tac_interestingness i1 i2 in
  let conv_logs = ExportTrace.conv_logs in
  let conv_rec_comp (_,_,i1) (_,_,i2) = ExportTrace.compare_conv_interestingness i1 i2 in

  Sys.mkdir dir_path 0o777;
  let string_of_asm_list l =
    (List.map (fun th -> "\"" ^ String.escaped (string_of_term (concl (snd th))) ^ "\"") l) in

  Hashtbl.iter (fun tac recs ->
      let recs = List.sort tac_rec_comp recs in
      let path = dir_path ^ "/" ^ tac ^ ".json" in
      let oc = open_out path in

      Printf.fprintf oc "[\n";
      List.iteri (fun i ((r:ExportTrace.tac_record),(r_args:ExportTrace.record_args),_) ->
          Printf.fprintf oc "  {\n";
          Printf.fprintf oc "    \"tactic\":\"%s\",\n" tac;
          Printf.fprintf oc "    \"definition_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.definition_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.definition_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"user_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.user_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.user_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"arg_names\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.names));
          Printf.fprintf oc "    \"arg_types\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.types));
          Printf.fprintf oc "    \"arg_values\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.values));
          Printf.fprintf oc "    \"arg_exprs\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.exprs));
          Printf.fprintf oc "    \"goal_before\": \"%s\",\n"
            (String.escaped (Format.asprintf "%a" pp_print_goal r.goal_before));
          Printf.fprintf oc "    \"goals_after\": [%s],\n"
            (String.concat ", " (List.map (fun g ->
              "{\"goal\": \"" ^
              String.escaped (Format.asprintf "%a" pp_print_goal g) ^
              "\", \"added_assumptions\": [" ^
              String.concat ","
                (string_of_asm_list (subtract (fst g) (fst r.goal_before))) ^
              "], \"removed_assumptions\": [" ^
              String.concat ","
                (string_of_asm_list (subtract (fst r.goal_before) (fst g))) ^
              "]}")
            r.goals_after));
          Printf.fprintf oc "    \"num_subgoals\": %d\n" r.num_subgoals;
          Printf.fprintf oc "  }%s\n" (if i + 1 = List.length recs then "" else ","))
        recs;
      Printf.fprintf oc "]\n";
      Printf.printf "Dumped to %s\n" path;
      close_out oc)
    tac_logs;

  Hashtbl.iter (fun conv recs ->
      let recs = List.sort conv_rec_comp recs in
      let path = dir_path ^ "/" ^ conv ^ ".json" in
      let oc = open_out path in

      Printf.fprintf oc "[\n";
      List.iteri (fun i ((r:ExportTrace.conv_record),(r_args:ExportTrace.record_args),_) ->
          Printf.fprintf oc "  {\n";
          Printf.fprintf oc "    \"conv\":\"%s\",\n" conv;
          Printf.fprintf oc "    \"definition_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.definition_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.definition_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"user_line_number\": {\n";
          Printf.fprintf oc "       \"file_path\": \"%s\",\n"
            (String.escaped (fst r.user_line_number));
          Printf.fprintf oc "       \"line\": %d\n" (snd r.user_line_number);
          Printf.fprintf oc "    },\n";
          Printf.fprintf oc "    \"arg_names\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.names));
          Printf.fprintf oc "    \"arg_types\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ s ^ "\"") r_args.types));
          Printf.fprintf oc "    \"arg_values\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.values));
          Printf.fprintf oc "    \"arg_exprs\": [%s],\n"
            (String.concat ", " (List.map (fun s -> "\"" ^ (String.escaped s) ^ "\"") r_args.exprs));
          Printf.fprintf oc "    \"output\": \"%s\"\n"
            (String.escaped (Format.asprintf "%a" pp_print_thm r.output));
          Printf.fprintf oc "  }%s\n" (if i + 1 = List.length recs then "" else ","))
        recs;
      Printf.fprintf oc "]\n";
      Printf.printf "Dumped to %s\n" path;
      close_out oc)
    conv_logs;;

(* a helper function *)
let rec to_n_elems (r:string list) n:string list =
  if n = 0 then []
  else match r with
  | h::t -> h::(to_n_elems t (n-1))
  | [] -> replicate "(unknown)" n;;


set_jrh_lexer;;
