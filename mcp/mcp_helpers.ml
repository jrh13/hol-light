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

let mcp_buf_json_string buf s =
  Buffer.add_char buf '"';
  String.iter (fun c -> match c with
    | '"'  -> Buffer.add_string buf "\\\""
    | '\\' -> Buffer.add_string buf "\\\\"
    | '\n' -> Buffer.add_string buf "\\n"
    | '\r' -> Buffer.add_string buf "\\r"
    | '\t' -> Buffer.add_string buf "\\t"
    | c when Char.code c < 0x20 ->
        Buffer.add_string buf (Printf.sprintf "\\u%04x" (Char.code c))
    | c -> Buffer.add_char buf c) s;
  Buffer.add_char buf '"';;

let mcp_buf_goal buf ((asl, w) : goal) =
  Buffer.add_string buf "{\"hypotheses\":[";
  let first = ref true in
  List.iter (fun (label, th) ->
    if !first then first := false else Buffer.add_char buf ',';
    Buffer.add_string buf "{\"label\":";
    mcp_buf_json_string buf label;
    Buffer.add_string buf ",\"term\":";
    mcp_buf_json_string buf (string_of_term (concl th));
    Buffer.add_char buf '}'
  ) (List.rev asl);
  Buffer.add_string buf "],\"conclusion\":";
  mcp_buf_json_string buf (string_of_term w);
  Buffer.add_char buf '}';;

let mcp_buf_goals buf gl =
  Buffer.add_char buf '[';
  let first = ref true in
  List.iter (fun g ->
    if !first then first := false else Buffer.add_char buf ',';
    mcp_buf_goal buf g
  ) gl;
  Buffer.add_char buf ']';;

let mcp_json_goalstate () =
  let buf = Buffer.create 256 in
  (match !current_goalstack with
  | [] ->
    Buffer.add_string buf "{\"goals\":[],\"num_subgoals\":0,\"total_goals\":0}"
  | [_, gl, _] ->
    let n = List.length gl in
    Buffer.add_string buf "{\"goals\":";
    mcp_buf_goals buf gl;
    Buffer.add_string buf ",\"num_subgoals\":";
    Buffer.add_string buf (string_of_int (min 1 n));
    Buffer.add_string buf ",\"total_goals\":";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf '}'
  | (_, gl, _) :: (_, gl0, _) :: _ ->
    let n = List.length gl in
    let p = n - List.length gl0 in
    let num_sub = if p < 1 then 1 else p + 1 in
    Buffer.add_string buf "{\"goals\":";
    mcp_buf_goals buf gl;
    Buffer.add_string buf ",\"num_subgoals\":";
    Buffer.add_string buf (string_of_int num_sub);
    Buffer.add_string buf ",\"total_goals\":";
    Buffer.add_string buf (string_of_int n);
    Buffer.add_char buf '}');
  Buffer.contents buf;;

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
  let buf = Buffer.create 512 in
  Buffer.add_char buf '[';
  let first = ref true in
  let count = ref 0 in
  List.iter (fun (n, th) ->
    if !count < limit then begin
      if !first then first := false else Buffer.add_char buf ',';
      Buffer.add_string buf "{\"name\":";
      mcp_buf_json_string buf n;
      Buffer.add_string buf ",\"statement\":";
      mcp_buf_json_string buf (string_of_thm th);
      Buffer.add_char buf '}';
      incr count
    end
  ) results;
  Buffer.add_char buf ']';
  Buffer.contents buf;;

let mcp_json_apply_tactics (tacs : tactic list) =
  let steps = ref 0 in
  try
    let proved = ref false in
    List.iter (fun tac ->
      if not !proved then begin
        ignore (e tac);
        incr steps;
        match !current_goalstack with
        | (_, [], _) :: _ -> proved := true
        | _ -> ()
      end
    ) tacs;
    if !proved then
      let th = match !current_goalstack with
        | (_, [], f) :: _ -> f null_inst []
        | _ -> failwith "unreachable" in
      "{\"proved\":true,\"theorem\":" ^ mcp_json_string (string_of_thm th) ^
      ",\"steps\":" ^ string_of_int !steps ^ "}"
    else
      let gs = mcp_json_goalstate () in
      let n = String.length gs in
      String.sub gs 0 (n - 1) ^ ",\"steps\":" ^ string_of_int !steps ^ "}"
  with
  | Failure msg ->
    "{\"error\":" ^ mcp_json_string msg ^
    ",\"step\":" ^ string_of_int !steps ^ "}"
  | e ->
    "{\"error\":" ^ mcp_json_string (Printexc.to_string e) ^
    ",\"step\":" ^ string_of_int !steps ^ "}";;

Printf.printf "MCP helpers loaded.\n%!";;
