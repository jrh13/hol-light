(* ========================================================================= *)
(*  Tactician Light                                                          *)
(*                                                                           *)
(*  A proof format translator for HOL Light, converting between              *)
(*  interactive (g/e) and structured (prove) proof styles.                   *)
(*                                                                           *)
(*  Inspired by Mark Adams' Tactician tool for HOL Light:                    *)
(*    http://www.proof-technologies.com/tactician/                           *)
(*  which provided similar functionality via a "hiproof"                     *)
(*  representation and refactoring pipeline. This is a from-scratch          *)
(*  reimplementation using string-based tactic recording rather than         *)
(*  the original promotion/demotion mechanism.                               *)
(*                                                                           *)
(* ========================================================================= *)
(*                                                                           *)
(*  USAGE                                                                    *)
(*                                                                           *)
(*  Load into a HOL Light session:                                           *)
(*    loadt "tactician_light.ml";;                                           *)
(*                                                                           *)
(*  --- Interactive proof development (interactive -> structured) ---        *)
(*                                                                           *)
(*  Record a proof interactively, then extract the structured form:          *)
(*                                                                           *)
(*    xg `!x:num. x = x`;;        (* set goal, start recording *)            *)
(*    xe "GEN_TAC";;               (* execute + record tactic *)             *)
(*    xe "REFL_TAC";;              (* execute + record tactic *)             *)
(*    xt();;                       (* print structured proof *)              *)
(*    xs();;                       (* return as string *)                    *)
(*                                                                           *)
(*  Other recording commands:                                                *)
(*    re "name" tac;;    execute tactic value + record with given name       *)
(*    xb();;             undo last recorded step                             *)
(*    xr n;;             record rotation (same as r n but recorded)          *)
(*    xp();;             print current recording                             *)
(*    xreset();;         reset recording                                     *)
(*    xshow();;          show goal, recording, and structured proof          *)
(*                                                                           *)
(*  --- Structured proof flattening (structured -> interactive) ---          *)
(*                                                                           *)
(*  Parse and execute a structured proof step by step:                       *)
(*                                                                           *)
(*    flatten_proof `!x:num. x = x` "GEN_TAC THEN REFL_TAC";;                *)
(*                                                                           *)
(*  --- File-level batch conversion ---                                      *)
(*                                                                           *)
(*  Convert entire files between formats:                                    *)
(*                                                                           *)
(*    s2i "structured.ml" "interactive.ml";;                                 *)
(*      Reads prove(...) blocks, flattens each to g/e commands.              *)
(*      Input format:  let NAME = prove(`goal`, tactic);;                    *)
(*      Output format: g `goal`;; e(tac1);; ... let NAME = top_thm();;       *)
(*                                                                           *)
(*    i2s "interactive.ml" "structured.ml";;                                 *)
(*      Reads g/e commands, replays through HOL Light, outputs prove.        *)
(*      Input format:  g `goal`;; e(tac1);; e(tac2);;                        *)
(*      Output format: let NAME = prove(`goal`, tac1 THEN tac2);;            *)
(*                                                                           *)
(*  The i2s direction extracts tactic strings from e(...) expressions        *)
(*  automatically -- no manual stringification needed. It also handles       *)
(*  b();; for undo, r n;; for rotation, p();; (skipped), and                 *)
(*  let NAME = top_thm();; for naming.                                       *)
(*                                                                           *)
(*  THEN optimization: when all THENL branches are identical, the            *)
(*  structured output uses THEN instead. Common head tactics are also        *)
(*  factored out across branches.                                            *)
(*                                                                           *)
(*  Output is formatted to stay within 78 columns where possible,            *)
(*  packing short tactics on one line in HOL Light house style.              *)
(*                                                                           *)
(*  KNOWN LIMITATIONS                                                        *)
(*                                                                           *)
(*  - Cross-level rotations (i2s direction): if r n rotates goals            *)
(*    from different tree depths past each other (e.g. doing r 2             *)
(*    when the stack has [A_sub1, A_sub2, B] to work on B first),            *)
(*    the tree builder will misassign tactics to branches. Same-level        *)
(*    rotations (reordering siblings) work correctly.                        *)
(*                                                                           *)
(*  - Type annotations in xt()/xs(): the interactive commands use            *)
(*    string_of_term on the goal, which may drop type annotations            *)
(*    needed for the output to reparse. The file-level i2s preserves         *)
(*    the original goal string and does not have this problem.               *)
(*                                                                           *)
(*  - Multi-proof files with dependencies: s2i and i2s process proofs        *)
(*    sequentially but do not bind theorem names between proofs. If          *)
(*    proof N references a name defined by proof N-1, conversion will        *)
(*    fail. Workaround: convert one proof at a time, or ensure proofs        *)
(*    are self-contained.                                                    *)
(*                                                                           *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(*  Tactic string scanner                                                    *)
(*                                                                           *)
(*  Bracket, backtick and string-aware character-by-character scanner        *)
(*  used throughout for parsing tactic expressions.                          *)
(* ------------------------------------------------------------------------- *)

let is_ident_char c = match c with
  | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' | '\'' -> true
  | _ -> false;;

type scan_st = {
  s_pd: int;
  s_bd: int;
  s_bt: bool;
  s_st: bool;
};;

let scan0 = { s_pd=0; s_bd=0; s_bt=false; s_st=false };;

let scan_char ss c =
  if ss.s_st then
    (if c = '"' then { ss with s_st = false } else ss)
  else if ss.s_bt then
    (if c = '`' then { ss with s_bt = false } else ss)
  else match c with
  | '"' -> { ss with s_st = true }
  | '`' -> { ss with s_bt = true }
  | '(' -> { ss with s_pd = ss.s_pd + 1 }
  | ')' -> { ss with s_pd = ss.s_pd - 1 }
  | '[' -> { ss with s_bd = ss.s_bd + 1 }
  | ']' -> { ss with s_bd = ss.s_bd - 1 }
  | _ -> ss;;

let at_top ss =
  ss.s_pd = 0 && ss.s_bd = 0 && not ss.s_bt && not ss.s_st;;

(* ------------------------------------------------------------------------- *)
(*  Proof tree data type and tactic evaluator                                *)
(* ------------------------------------------------------------------------- *)

type proof_tree =
  | Pstep of string * proof_tree list
  | Popen;;

let the__tac__ref = ref ALL_TAC;;

let eval_tactic (s:string) : tactic =
  let tmp = Filename.temp_file "hol_tac_" ".ml" in
  let oc = open_out tmp in
  Printf.fprintf oc "the__tac__ref := (%s);;\n" s;
  close_out oc;
  let old_tie = !type_invention_error in
  type_invention_error := false;
  (try loadt tmp
   with e -> (type_invention_error := old_tie;
              (try Sys.remove tmp with _ -> ()); raise e));
  type_invention_error := old_tie;
  (try Sys.remove tmp with _ -> ());
  !the__tac__ref;;

(* eval_and_apply: evaluate a tactic string AND apply it to the current      *)
(* goal in the same temp file context. This avoids a closure capture bug     *)
(* where tactics with FIRST_ASSUM/MATCH_MP/SET_RULE and invented type        *)
(* variables fail when the closure is built in one loadt and applied later.  *)
(* By doing e(tac) in the same temp file, values like SET_RULE results       *)
(* remain live when the tactic is applied to the goal.                       *)
let eval_and_apply (s:string) : unit =
  let tmp = Filename.temp_file "hol_tac_" ".ml" in
  let oc = open_out tmp in
  Printf.fprintf oc "e(%s);;\n" s;
  close_out oc;
  let old_tie = !type_invention_error in
  type_invention_error := false;
  (try loadt tmp
   with e -> (type_invention_error := old_tie;
              (try Sys.remove tmp with _ -> ()); raise e));
  type_invention_error := old_tie;
  (try Sys.remove tmp with _ -> ());;

(* ------------------------------------------------------------------------- *)
(*  Recording layer                                                          *)
(* ------------------------------------------------------------------------- *)

let tac_record : (string * int) list ref = ref [];;
let tac_goal : term ref = ref `T`;;

let num_goals () : int =
  try let (_,gls,_) = hd(!current_goalstack) in length gls
  with Failure _ -> 0;;

let xg tm =
  tac_record := [];
  tac_goal := tm;
  g tm;;

let xe (s:string) =
  let n0 = num_goals () in
  eval_and_apply s;
  let n1 = num_goals () in
  tac_record := !tac_record @ [(s, n1 - n0 + 1)];
  !current_goalstack;;

let re (s:string) (tac:tactic) =
  let n0 = num_goals () in
  let gs = e tac in
  let n1 = num_goals () in
  tac_record := !tac_record @ [(s, n1 - n0 + 1)];
  gs;;

let xb () =
  (match !tac_record with
   | [] -> ()
   | _ -> tac_record := rev (tl (rev !tac_record)));
  b();;

let xr n =
  let gs = r n in
  tac_record := !tac_record @ [("__ROTATE__", n)];
  gs;;

let xp () =
  let steps = !tac_record in
  if steps = [] then print_string "(no steps recorded)\n"
  else
    do_list (fun (s,n) ->
      if s = "__ROTATE__" then
        Printf.printf "  r %-48d\n" n
      else
        Printf.printf "  %-50s  [%d]\n" s n) steps;
  Printf.printf "  (%d steps total)\n%!" (length steps);;

(* ------------------------------------------------------------------------- *)
(*  Build proof tree from recording                                          *)
(* ------------------------------------------------------------------------- *)

let rec build_ptree steps =
  match steps with
  | [] -> (Popen, [])
  | (tac, n) :: rest ->
    if tac = "__ROTATE__" then build_ptree rest
    else if n <= 0 then (Pstep(tac, []), rest)
    else
      let children, remaining = build_ptree_children n rest in
      (Pstep(tac, children), remaining)

and build_ptree_children n steps =
  if n <= 0 then ([], steps)
  else
    let ids = ref [] in
    (for ii = n - 1 downto 0 do ids := ii :: !ids done);
    let queue = ref !ids in
    let s = ref steps in
    let pairs = ref [] in
    (for dummy = 1 to n do
      let keep_looping = ref true in
      (while !keep_looping do
        if !s = [] then keep_looping := false
        else if fst (hd !s) = "__ROTATE__" then
          (let k = snd (hd !s) in
           s := tl !s;
           let q = !queue in
           let ql = length q in
           let kk = ((k mod ql) + ql) mod ql in
           if kk > 0 then
             (let front = ref [] in
              let back = ref q in
              (for dummy2 = 1 to kk do
                front := hd !back :: !front;
                back := tl !back
              done);
              queue := !back @ rev !front)
           else ())
        else keep_looping := false
      done);
      let orig_idx = hd !queue in
      let (child, rest) = build_ptree !s in
      pairs := (orig_idx, child) :: !pairs;
      s := rest;
      queue := tl !queue
    done);
    let sorted = sort (fun (a,_) (b,_) -> a < b) (rev !pairs) in
    (map snd sorted, !s);;

let get_ptree () =
  let tree, left = build_ptree !tac_record in
  if left <> [] then
    Printf.printf "(* Warning: %d unused recording steps *)\n" (length left);
  tree;;

(* ------------------------------------------------------------------------- *)
(*  Proof tree equality and THEN optimization                                *)
(* ------------------------------------------------------------------------- *)

let rec ptree_eq t1 t2 = match t1, t2 with
  | Popen, Popen -> true
  | Pstep(s1,c1), Pstep(s2,c2) ->
    s1 = s2 && length c1 = length c2 && forall2 ptree_eq c1 c2
  | _ -> false;;

let all_ptree_eq = function
  | [] | [_] -> true
  | h :: t -> forall (ptree_eq h) t;;

let common_head trees =
  match trees with
  | [] -> None
  | Popen :: _ -> None
  | Pstep(h,_) :: rest ->
    if forall (fun t -> match t with
      | Pstep(s,_) -> s = h | _ -> false) rest
    then Some h
    else None;;

let factor_head trees =
  match common_head trees with
  | None -> None
  | Some h ->
    let children = map (fun t -> match t with
      | Pstep(_, cs) -> cs | _ -> []) trees in
    if forall (fun cs -> length cs = 1) children then
      Some(h, map hd children)
    else None;;

(* ------------------------------------------------------------------------- *)
(*  Pretty printer - proof tree to structured tactic string                  *)
(* ------------------------------------------------------------------------- *)

let pad n = String.make (max 0 n) ' ';;

(* Split a tactic string at top-level THEN (not THENL) keywords              *)
let split_at_then s =
  let len = String.length s in
  if len = 0 then [s]
  else
  let ss = ref scan0 in
  let parts = ref [] in
  let start = ref 0 in
  let i = ref 0 in
  while !i < len do
    ss := scan_char !ss s.[!i];
    if at_top !ss &&
       !i + 4 <= len &&
       String.sub s !i 4 = "THEN" &&
       (!i = 0 || not (is_ident_char s.[!i - 1])) &&
       (!i + 4 >= len || not (is_ident_char s.[!i + 4])) then (
      parts := String.trim (String.sub s !start (!i - !start)) :: !parts;
      i := !i + 4;
      while !i < len && (s.[!i] = ' ' || s.[!i] = '\n' ||
                          s.[!i] = '\r' || s.[!i] = '\t') do incr i done;
      start := !i
    ) else incr i
  done;
  let last = String.trim (String.sub s !start (len - !start)) in
  let parts = if last = "" then !parts else last :: !parts in
  rev parts;;

(* Format a tactic string to stay within 78 columns, starting at col.        *)
(* Greedily packs THEN-separated parts on lines, breaking when needed.       *)
let format_tac col tac =
  let parts = split_at_then tac in
  match parts with
  | [] -> tac
  | [_] -> tac
  | _ ->
    let buf = Buffer.create 256 in
    let cur_col = ref col in
    let is_first = ref true in
    do_list (fun part ->
      let plen = String.length part in
      if !is_first then (
        Buffer.add_string buf part;
        cur_col := col + plen;
        is_first := false
      ) else if !cur_col + 6 + plen <= 78 then (
        Buffer.add_string buf " THEN ";
        Buffer.add_string buf part;
        cur_col := !cur_col + 6 + plen
      ) else (
        Buffer.add_string buf " THEN\n";
        Buffer.add_string buf (pad col);
        Buffer.add_string buf part;
        cur_col := col + plen
      )
    ) parts;
    Buffer.contents buf;;

let rec render col tree =
  match tree with
  | Popen -> "CHEAT_TAC"
  | Pstep(tac, []) -> format_tac col tac
  | Pstep(tac, [child]) ->
    format_tac col tac ^ " THEN\n" ^ pad col ^ render col child
  | Pstep(tac, children) when all_ptree_eq children ->
    format_tac col tac ^ " THEN\n" ^ pad col ^ render col (hd children)
  | Pstep(tac, children) ->
    (match factor_head children with
     | Some(h, new_children) ->
       format_tac col tac ^ " THEN\n" ^ pad col ^
       render col (Pstep(h, new_children))
     | None ->
       let ic = col + 2 in
       format_tac col tac ^ " THENL\n" ^ pad (col + 1) ^
       "[" ^ String.concat (";\n" ^ pad ic)
               (map (render ic) children) ^ "]");;

let xt () =
  let tree = get_ptree () in
  let gs = string_of_term !tac_goal in
  let ts = render 2 tree in
  Printf.printf "let RESULT = prove\n (`%s`,\n  %s);;\n%!" gs ts;;

let xs () =
  let tree = get_ptree () in
  let gs = string_of_term !tac_goal in
  let ts = render 2 tree in
  Printf.sprintf "let RESULT = prove\n (`%s`,\n  %s);;" gs ts;;

let xreset () =
  tac_record := [];
  Printf.printf "(recording cleared)\n%!";;

let xshow () =
  Printf.printf "Goal: `%s`\n\n" (string_of_term !tac_goal);
  Printf.printf "Recording (%d steps):\n" (length !tac_record);
  xp();
  Printf.printf "\nStructured proof:\n";
  xt();;

(* ------------------------------------------------------------------------- *)
(*  Tactic string parser (structured -> interactive)                         *)
(*                                                                           *)
(*  Parses a tactic expression, finding THENL branching structure            *)
(*  and let...in bindings. THEN chains are kept as atomic strings.           *)
(* ------------------------------------------------------------------------- *)

type ftree =
  | Fleaf of string
  | Fbranch of string * ftree list
  | Fafter of ftree * ftree
  | Flet of string * ftree;;

(* Find first top-level THENL in string s                                    *)
(* Returns Some(prefix, bracket_contents, suffix) or None                    *)
let find_thenl s =
  let len = String.length s in
  let ss = ref scan0 in
  let result = ref None in
  let i = ref 0 in
  while !i < len && !result = None do
    ss := scan_char !ss s.[!i];
    if at_top !ss && !i + 5 <= len then begin
      let before_ok = (!i = 0 || not (is_ident_char s.[!i - 1])) in
      if before_ok &&
         !i + 5 <= len && String.sub s !i 5 = "THENL" &&
         (!i + 5 >= len || not (is_ident_char s.[!i + 5])) then
      begin
        let prefix = String.trim (String.sub s 0 !i) in
        let j = ref (!i + 5) in
        while !j < len && (s.[!j] = ' ' || s.[!j] = '\n' ||
                           s.[!j] = '\r' || s.[!j] = '\t') do
          incr j
        done;
        if !j < len && s.[!j] = '[' then begin
          let bstart = !j + 1 in
          let depth = ref 1 in
          let bs = ref scan0 in
          let k = ref bstart in
          while !k < len && !depth > 0 do
            bs := scan_char !bs s.[!k];
            if not (!bs).s_bt && not (!bs).s_st && (!bs).s_pd = 0 then begin
              if s.[!k] = '[' then incr depth
              else if s.[!k] = ']' then decr depth
            end;
            if !depth > 0 then incr k
          done;
          let bcontent = String.sub s bstart (!k - bstart) in
          let rest = if !k + 1 < len
            then String.trim (String.sub s (!k + 1) (len - !k - 1))
            else "" in
          let suffix =
            let rlen = String.length rest in
            if rlen >= 4 && String.sub rest 0 4 = "THEN" &&
               (rlen = 4 || not (is_ident_char rest.[4])) &&
               not (rlen >= 5 && String.sub rest 0 5 = "THENL") then
              String.trim (String.sub rest 4 (rlen - 4))
            else rest in
          result := Some(prefix, bcontent, suffix)
        end
      end
    end;
    incr i
  done;
  !result;;

(* Split string at top-level semicolons                                      *)
let split_semis s =
  let len = String.length s in
  let ss = ref scan0 in
  let parts = ref [] in
  let start = ref 0 in
  for i = 0 to len - 1 do
    ss := scan_char !ss s.[i];
    if at_top !ss && s.[i] = ';' then begin
      parts := String.trim (String.sub s !start (i - !start)) :: !parts;
      start := i + 1
    end
  done;
  let last = String.trim (String.sub s !start (len - !start)) in
  let parts = if last = "" then !parts else last :: !parts in
  rev parts;;

(* Find top-level 'let ... in' binding                                       *)
let find_let_in s =
  let len = String.length s in
  if len < 6 || String.sub s 0 4 <> "let " then None
  else
    let ss = ref scan0 in
    let depth = ref 0 in
    let result = ref None in
    let i = ref 0 in
    while !i < len && !result = None do
      ss := scan_char !ss s.[!i];
      if at_top !ss then (
        if !i + 3 <= len && String.sub s !i 3 = "let" &&
           (!i = 0 || not (is_ident_char s.[!i - 1])) &&
           (!i + 3 >= len || not (is_ident_char s.[!i + 3])) then
          depth := !depth + 1;
        if !i + 2 <= len && String.sub s !i 2 = "in" &&
           (!i = 0 || not (is_ident_char s.[!i - 1])) &&
           (!i + 2 >= len || not (is_ident_char s.[!i + 2])) then (
          depth := !depth - 1;
          if !depth = 0 then
            result := Some !i
        )
      );
      incr i
    done;
    match !result with
    | None -> None
    | Some pos ->
      let binding = String.trim (String.sub s 0 pos) in
      let body = String.trim (String.sub s (pos + 2) (len - pos - 2)) in
      Some(binding, body);;

let rec parse_tac s =
  let s = String.trim s in
  match find_let_in s with
  | Some(binding, body) -> Flet(binding, parse_tac body)
  | None ->
  match find_thenl s with
  | None -> Fleaf s
  | Some(prefix, content, suffix) ->
    let branches = split_semis content in
    let core = Fbranch(String.trim prefix,
                       map parse_tac branches) in
    if suffix = "" then core
    else Fafter(core, parse_tac suffix);;

(* ------------------------------------------------------------------------- *)
(*  Flatten structured proof to interactive form                             *)
(* ------------------------------------------------------------------------- *)

let rec flatten_step prefix tree =
  match tree with
  | Fleaf s ->
    Printf.printf "%se(%s);;\n%!" prefix s;
    let n0 = num_goals () in
    eval_and_apply s;
    let n1 = num_goals () in
    n1 - n0 + 1
  | Fbranch(pre, branches) ->
    Printf.printf "%se(%s);;\n%!" prefix pre;
    let n0 = num_goals () in
    eval_and_apply pre;
    let n1 = num_goals () in
    let nbranch = n1 - n0 + 1 in
    if nbranch <> length branches then
      (Printf.printf
        "(* ERROR: %s produced %d subgoals but THENL has %d branches *)\n"
        pre nbranch (length branches);
      nbranch)
    else
      let total = ref 0 in
      let idx = ref 1 in
      do_list (fun branch ->
        Printf.printf "%s(* branch %d of %d *)\n%!" prefix !idx nbranch;
        let m = flatten_step prefix branch in
        total := !total + m;
        incr idx
      ) branches;
      !total
  | Fafter(main, suffix) ->
    (match main with
     | Fbranch(pre, branches) ->
       flatten_step prefix
         (Fbranch(pre, map (fun b -> Fafter(b, suffix)) branches))
     | _ ->
       let remaining = flatten_step prefix main in
       if remaining = 0 then 0
       else
         let total = ref 0 in
         for dummy = 1 to remaining do
           let m = flatten_step prefix suffix in
           total := !total + m
         done;
         !total)
  | Flet(binding, body) ->
    Printf.printf "%s%s;;\n%!" prefix binding;
    let tmp = Filename.temp_file "hol_let_" ".ml" in
    let oc = open_out tmp in
    Printf.fprintf oc "%s;;\n" binding;
    close_out oc;
    (try loadt tmp
     with e -> (try Sys.remove tmp with _ -> ()); raise e);
    (try Sys.remove tmp with _ -> ());
    flatten_step prefix body;;

let flatten_proof tm tac_str =
  let _ = g tm in
  let tree = parse_tac tac_str in
  Printf.printf "g `%s`;;\n\n%!" (string_of_term tm);
  let remaining = flatten_step "" tree in
  if remaining = 0 then
    Printf.printf "\n(* Proof complete. *)\n%!"
  else
    Printf.printf "\n(* %d subgoals remaining *)\n%!" remaining;;

(* ------------------------------------------------------------------------- *)
(*  File-level proof format conversion                                       *)
(* ------------------------------------------------------------------------- *)

let read_whole_file fn =
  let ic = Stdlib.open_in fn in
  let n = in_channel_length ic in
  let buf = Buffer.create n in
  (try while true do Buffer.add_char buf (input_char ic) done
   with End_of_file -> ());
  Stdlib.close_in ic;
  Buffer.contents buf;;

let write_whole_file fn s =
  let oc = open_out fn in
  output_string oc s;
  close_out oc;;

(* --- Bracket-aware scanning for file parsing ---                           *)

let find_backtick s i =
  let len = String.length s in
  let j = ref i in
  while !j < len && s.[!j] <> '`' do incr j done;
  if !j < len then !j else -1;;

let find_close_paren s start =
  let len = String.length s in
  let dep = ref 1 in
  let in_str = ref false in
  let in_bt = ref false in
  let cmt = ref 0 in
  let i = ref start in
  while !i < len && !dep > 0 do
    let c = s.[!i] in
    if !in_str then
      (if c = '\\' && !i + 1 < len then incr i
       else if c = '"' then in_str := false)
    else if !in_bt then
      (if c = '`' then in_bt := false)
    else if !cmt > 0 then
      (if c = '(' && !i + 1 < len && s.[!i+1] = '*' then
        (cmt := !cmt + 1; incr i)
      else if c = '*' && !i + 1 < len && s.[!i+1] = ')' then
        (cmt := !cmt - 1; incr i))
    else
      (if c = '"' then in_str := true
       else if c = '`' then in_bt := true
       else if c = '(' && !i + 1 < len && s.[!i+1] = '*' then
         (cmt := 1; incr i)
       else if c = '(' then dep := !dep + 1
       else if c = ')' then dep := !dep - 1);
    if !dep > 0 then incr i
  done;
  if !dep = 0 then !i else -1;;

let find_double_semi s i =
  let len = String.length s in
  let j = ref i in
  while !j < len - 1 && not (s.[!j] = ';' && s.[!j+1] = ';') do
    incr j
  done;
  if !j < len - 1 then !j else -1;;

let string_has_sub s sub =
  let slen = String.length s in
  let sublen = String.length sub in
  let found = ref false in
  let i = ref 0 in
  while !i <= slen - sublen && not !found do
    if String.sub s !i sublen = sub then found := true
    else incr i
  done;
  !found;;

(* --- Flatten to buffer (used by s2i) ---                                   *)

let rec flatten_to_buf buf prefix tree =
  match tree with
  | Fleaf s ->
    Buffer.add_string buf (Printf.sprintf "%se(%s);;\n" prefix s);
    let n0 = num_goals () in
    eval_and_apply s;
    let n1 = num_goals () in
    n1 - n0 + 1
  | Fbranch(pre, branches) ->
    Buffer.add_string buf (Printf.sprintf "%se(%s);;\n" prefix pre);
    let n0 = num_goals () in
    eval_and_apply pre;
    let n1 = num_goals () in
    let nbranch = n1 - n0 + 1 in
    if nbranch <> length branches then
      (Buffer.add_string buf (Printf.sprintf
        "%s(* ERROR: %s produced %d subgoals but THENL has %d branches *)\n"
        prefix pre nbranch (length branches));
      nbranch)
    else
      let total = ref 0 in
      let idx = ref 1 in
      do_list (fun branch ->
        Buffer.add_string buf (Printf.sprintf
          "%s(* branch %d of %d *)\n" prefix !idx nbranch);
        let m = flatten_to_buf buf prefix branch in
        total := !total + m;
        incr idx
      ) branches;
      !total
  | Fafter(main, suffix) ->
    (match main with
     | Fbranch(pre, branches) ->
       flatten_to_buf buf prefix
         (Fbranch(pre, map (fun b -> Fafter(b, suffix)) branches))
     | _ ->
       let remaining = flatten_to_buf buf prefix main in
       if remaining = 0 then 0
       else
         let total = ref 0 in
         for dummy = 1 to remaining do
           let m = flatten_to_buf buf prefix suffix in
           total := !total + m
         done;
         !total)
  | Flet(binding, body) ->
    Buffer.add_string buf (Printf.sprintf "%s%s;;\n" prefix binding);
    let tmp = Filename.temp_file "hol_let_" ".ml" in
    let oc = open_out tmp in
    Printf.fprintf oc "%s;;\n" binding;
    close_out oc;
    (try loadt tmp
     with e -> (try Sys.remove tmp with _ -> ()); raise e);
    (try Sys.remove tmp with _ -> ());
    flatten_to_buf buf prefix body;;

(* --- Parse interactive proof file ---                                      *)

let parse_interactive content =
  let len = String.length content in
  let proofs = ref [] in
  let cur_name = ref (None : string option) in
  let cur_goal = ref "" in
  let cur_steps = ref ([] : string list) in
  let flush () =
    if !cur_goal <> "" then (
      proofs := (!cur_name, !cur_goal, rev !cur_steps) :: !proofs;
      cur_name := None; cur_goal := ""; cur_steps := []) in
  let i = ref 0 in
  while !i < len do
    while !i < len &&
      (let c = content.[!i] in
       c = ' ' || c = '\n' || c = '\r' || c = '\t') do incr i done;
    if !i >= len then ()
    else if !i + 1 < len && content.[!i] = '(' && content.[!i+1] = '*'
    then (
      let d = ref 1 in
      i := !i + 2;
      while !i < len - 1 && !d > 0 do
        if content.[!i] = '(' && content.[!i+1] = '*' then
          (d := !d + 1; i := !i + 2)
        else if content.[!i] = '*' && content.[!i+1] = ')' then
          (d := !d - 1; i := !i + 2)
        else incr i
      done)
    else if content.[!i] = 'g' && !i + 1 < len &&
       not (is_ident_char content.[!i+1]) then (
      flush ();
      let j = find_backtick content (!i + 1) in
      if j >= 0 then (
        let j2 = find_backtick content (j + 1) in
        if j2 >= 0 then (
          cur_goal := String.sub content (j + 1) (j2 - j - 1);
          let semi = find_double_semi content (j2 + 1) in
          i := (if semi >= 0 then semi + 2 else j2 + 1))
        else i := j + 1)
      else incr i)
    else if content.[!i] = 'b' && !i + 1 < len &&
            not (is_ident_char content.[!i+1]) then (
      let semi = find_double_semi content (!i + 1) in
      let arg = String.trim (String.sub content (!i + 1)
        ((if semi >= 0 then semi else len) - !i - 1)) in
      if arg = "()" then (
        (match !cur_steps with
         | [] -> ()
         | _ :: rest -> cur_steps := rest);
        i := (if semi >= 0 then semi + 2 else len))
      else
        i := (if semi >= 0 then semi + 2 else len))
    else if content.[!i] = 'r' && !i + 1 < len &&
            not (is_ident_char content.[!i+1]) then (
      let semi = find_double_semi content (!i + 1) in
      if semi >= 0 then (
        let arg = String.trim (String.sub content (!i + 1) (semi - !i - 1)) in
        let arg = let al = String.length arg in
          if al >= 2 && arg.[0] = '(' && arg.[al - 1] = ')' then
            String.trim (String.sub arg 1 (al - 2))
          else arg in
        (try let n = int_of_string arg in
           cur_steps := ("__ROTATE__ " ^ string_of_int n) :: !cur_steps
         with _ -> ());
        i := semi + 2)
      else incr i)
    else if content.[!i] = 'p' && !i + 1 < len &&
            not (is_ident_char content.[!i+1]) then (
      let semi = find_double_semi content (!i + 1) in
      i := (if semi >= 0 then semi + 2 else len))
    else if content.[!i] = 'e' && !i + 1 < len &&
            content.[!i+1] = '(' then (
      let pend = find_close_paren content (!i + 2) in
      if pend >= 0 then (
        let tac = String.trim
          (String.sub content (!i + 2) (pend - !i - 2)) in
        cur_steps := tac :: !cur_steps;
        let semi = find_double_semi content (pend + 1) in
        i := (if semi >= 0 then semi + 2 else pend + 1))
      else incr i)
    else if !i + 4 < len && String.sub content !i 4 = "let " then (
      let semi = find_double_semi content !i in
      if semi >= 0 then (
        let chunk = String.sub content !i (semi - !i) in
        if string_has_sub chunk "top_thm" then (
          let j = ref 4 in
          while !j < String.length chunk &&
            (chunk.[!j] = ' ' || chunk.[!j] = '\n') do incr j done;
          let nstart = !j in
          while !j < String.length chunk &&
            is_ident_char chunk.[!j] do incr j done;
          if !j > nstart then
            cur_name := Some (String.sub chunk nstart (!j - nstart)));
        i := semi + 2)
      else incr i)
    else (
      let semi = find_double_semi content !i in
      if semi >= 0 then i := semi + 2
      else (while !i < len && content.[!i] <> '\n' do incr i done;
            if !i < len then incr i))
  done;
  flush ();
  rev !proofs;;

(* --- Parse structured proof file ---                                       *)

let parse_structured content =
  let len = String.length content in
  let proofs = ref [] in
  let i = ref 0 in
  let in_str = ref false in
  let in_bt = ref false in
  let cmt = ref 0 in
  let dep = ref 0 in
  while !i < len do
    let c = content.[!i] in
    if !in_str then
      (if c = '\\' && !i + 1 < len then incr i
       else if c = '"' then in_str := false)
    else if !in_bt then
      (if c = '`' then in_bt := false)
    else if !cmt > 0 then
      (if c = '(' && !i + 1 < len && content.[!i+1] = '*' then
        (cmt := !cmt + 1; incr i)
      else if c = '*' && !i + 1 < len && content.[!i+1] = ')' then
        (cmt := !cmt - 1; incr i))
    else (
      (match c with
       | '"' -> in_str := true
       | '`' -> in_bt := true
       | '(' when !i + 1 < len && content.[!i+1] = '*' ->
         cmt := 1; incr i
       | '(' -> dep := !dep + 1
       | ')' -> dep := !dep - 1
       | _ -> ());
      if !dep = 0 && !cmt = 0 && not !in_str && not !in_bt &&
         !i + 5 <= len && String.sub content !i 5 = "prove" &&
         (!i = 0 || not (is_ident_char content.[!i-1])) &&
         (!i + 5 >= len || not (is_ident_char content.[!i+5]))
      then (
        let name = ref "RESULT" in
        let j = ref (!i - 1) in
        while !j >= 0 && (let ch = content.[!j] in
          ch = ' ' || ch = '\n' || ch = '\r' || ch = '\t' ||
          ch = '=') do decr j done;
        let ne = !j + 1 in
        while !j >= 0 && is_ident_char content.[!j] do decr j done;
        let ns = !j + 1 in
        if ns < ne then name := String.sub content ns (ne - ns);
        let k = ref (!i + 5) in
        while !k < len && content.[!k] <> '(' do incr k done;
        if !k < len then (
          let pstart = !k + 1 in
          let bt1 = find_backtick content pstart in
          if bt1 >= 0 then (
            let bt2 = find_backtick content (bt1 + 1) in
            if bt2 >= 0 then (
              let goal = String.sub content (bt1 + 1) (bt2 - bt1 - 1) in
              let m = ref (bt2 + 1) in
              while !m < len && (let ch = content.[!m] in
                ch = ' ' || ch = '\n' || ch = '\r' || ch = '\t' ||
                ch = ',') do incr m done;
              let pend = find_close_paren content pstart in
              if pend >= 0 then (
                let tac = String.trim
                  (String.sub content !m (pend - !m)) in
                proofs := (!name, goal, tac) :: !proofs;
                i := pend + 1)
              else i := !m)
            else i := bt1 + 1)
          else i := pstart)
        else i := !k)
    );
    incr i
  done;
  rev !proofs;;

(* --- i2s: interactive to structured ---                                    *)

let i2s infile outfile =
  let content = read_whole_file infile in
  let proofs = parse_interactive content in
  if proofs = [] then
    (Printf.printf "No proof blocks found in %s\n%!" infile; ())
  else
  let buf = Buffer.create 4096 in
  do_list (fun (name, goal, steps) ->
    let nm = (match name with Some n -> n | None -> "RESULT") in
    Printf.printf "Converting %s ...\n%!" nm;
    let tm = parse_term goal in
    let _ = xg tm in
    do_list (fun s ->
      let rp = "__ROTATE__ " in
      let rplen = String.length rp in
      if String.length s > rplen &&
         String.sub s 0 rplen = rp then
        (let n = int_of_string (String.sub s rplen
           (String.length s - rplen)) in
         Printf.printf "  r %d\n%!" n;
         let _ = xr n in ())
      else
        (Printf.printf "  xe %s\n%!"
          (String.sub s 0 (min 60 (String.length s)));
         let _ = xe s in ())) steps;
    if num_goals () <> 0 then
      Printf.printf "  WARNING: %d subgoals remaining\n%!"
        (num_goals ());
    let tree = get_ptree () in
    let ts = render 2 tree in
    Buffer.add_string buf
      (Printf.sprintf "let %s = prove\n (`%s`,\n  %s);;\n\n"
        nm goal ts)
  ) proofs;
  write_whole_file outfile (Buffer.contents buf);
  Printf.printf "Wrote %d proof(s) to %s\n%!" (length proofs) outfile;;

(* --- s2i: structured to interactive ---                                    *)

let s2i infile outfile =
  let content = read_whole_file infile in
  let proofs = parse_structured content in
  if proofs = [] then
    (Printf.printf "No prove(...) blocks found in %s\n%!" infile; ())
  else
  let buf = Buffer.create 4096 in
  do_list (fun (name, goal, tac_str) ->
    Printf.printf "Converting %s ...\n%!" name;
    let tm = parse_term goal in
    let _ = g tm in
    Buffer.add_string buf
      (Printf.sprintf "(* %s *)\ng `%s`;;\n" name goal);
    let tree = parse_tac tac_str in
    let remaining = flatten_to_buf buf "" tree in
    if remaining = 0 then
      Buffer.add_string buf
        (Printf.sprintf "let %s = top_thm();;\n\n" name)
    else
      Buffer.add_string buf
        (Printf.sprintf "(* %d subgoals remaining *)\n\n" remaining)
  ) proofs;
  write_whole_file outfile (Buffer.contents buf);
  Printf.printf "Wrote %d proof(s) to %s\n%!" (length proofs) outfile;;
