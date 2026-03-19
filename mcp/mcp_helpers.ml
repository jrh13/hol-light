(* MCP helpers: JSON serialization for HOL Light goal states.
   Loaded via #use after HOL Light starts. No external dependencies. *)

let mcp_json_escape s =
  let buf = Buffer.create (String.length s + 16) in
  String.iter (fun c -> match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.contents buf;;

let mcp_json_string s = "\"" ^ mcp_json_escape s ^ "\"";;

let mcp_json_error msg = "{\"error\":" ^ mcp_json_string msg ^ "}";;

let mcp_json_goal ((asl, w) : goal) =
  let hyps = List.rev_map (fun (label, th) ->
    "{\"label\":" ^ mcp_json_string label ^
    ",\"term\":" ^ mcp_json_string (string_of_term (concl th)) ^ "}"
  ) asl in
  "{\"hypotheses\":[" ^ String.concat "," (List.rev hyps) ^
  "],\"conclusion\":" ^ mcp_json_string (string_of_term w) ^ "}";;

let mcp_json_goalstate () =
  match !current_goalstack with
  | [] -> "{\"goals\":[],\"num_subgoals\":0,\"total_goals\":0}"
  | [_, gl, _] ->
    let n = List.length gl in
    "{\"goals\":[" ^ String.concat "," (List.map mcp_json_goal gl) ^
    "],\"num_subgoals\":" ^ string_of_int (min 1 n) ^
    ",\"total_goals\":" ^ string_of_int n ^ "}"
  | (_, gl, _) :: (_, gl0, _) :: _ ->
    let n = List.length gl in
    let p = n - List.length gl0 in
    let num_sub = if p < 1 then 1 else p + 1 in
    "{\"goals\":[" ^ String.concat "," (List.map mcp_json_goal gl) ^
    "],\"num_subgoals\":" ^ string_of_int num_sub ^
    ",\"total_goals\":" ^ string_of_int n ^ "}";;

(* Apply tactic: called after Python evals "e(TACTIC);;" successfully.
   Checks if proof is complete, otherwise returns goal state. *)
let mcp_json_after_tactic () =
  match !current_goalstack with
  | (_, [], f) :: _ ->
    let th = f null_inst [] in
    "{\"proved\":true,\"theorem\":" ^ mcp_json_string (string_of_thm th) ^ "}"
  | _ -> mcp_json_goalstate ();;

let mcp_json_backtrack n =
  try
    for _ = 1 to n do ignore (b ()) done;
    mcp_json_goalstate ()
  with
  | Failure msg -> mcp_json_error msg
  | e -> mcp_json_error (Printexc.to_string e);;

let mcp_json_search pat limit =
  let results = search [name pat] in
  let take n l =
    let rec aux acc n = function
      | _ when n <= 0 -> List.rev acc
      | [] -> List.rev acc
      | x :: xs -> aux (x :: acc) (n - 1) xs in
    aux [] n l in
  let entries = List.map (fun (n, th) ->
    "{\"name\":" ^ mcp_json_string n ^
    ",\"statement\":" ^ mcp_json_string (string_of_thm th) ^ "}"
  ) (take limit results) in
  "[" ^ String.concat "," entries ^ "]";;

Printf.printf "MCP helpers loaded.\n%!";;
