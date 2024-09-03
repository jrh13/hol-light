(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2024                       *)
(*              (c) Copyright, Juneyoung Lee 2024                            *)
(* ========================================================================= *)

if Array.length Sys.argv <> 3 then
  let _ = Printf.eprintf "inline_load.ml <input.ml> <output.ml>\n" in
  exit 1;;

let filename = Sys.argv.(1);;
let fout = open_out (Sys.argv.(2));;

#use "hol_loader.ml";;

let parse_load_statement fnname stmt: (string * string) option =
  let stmt = String.trim stmt in
  if not (String.starts_with ~prefix:fnname stmt) then None else
  let n = String.length fnname in
  let stmt = String.trim (String.sub stmt n (String.length stmt - n)) in
  if not (stmt.[0] = '"') then None else
  let stmt = String.sub stmt 1 (String.length stmt - 1) in
  let idx = String.index stmt '"' in
  if idx = -1 then None else
  let path = String.sub stmt 0 idx in
  let stmt = String.sub stmt (idx + 1) (String.length stmt - idx - 1) in
  let stmt = String.trim stmt in
  if not (String.starts_with ~prefix:";;" stmt) then None else
  let stmt = String.sub stmt 2 (String.length stmt - 2) in
  Some (path,stmt);;


let strings_of_file filename =
  let fd =
    try open_in filename
    with Sys_error _ -> failwith("strings_of_file: can't open "^filename) in
  let rec suck_lines acc =
    let l = try [input_line fd] with End_of_file -> [] in
     if l = [] then List.rev acc else suck_lines(List.hd l::acc) in
  let data = suck_lines [] in
  (close_in fd; data);;

file_loader := fun filename ->
  let open Printf in
  fprintf fout "(* %s *)\n" filename;
  let lines = strings_of_file filename in
  List.iter
    (fun line ->
      match parse_load_statement "loadt" line with
      | Some (path,line') -> loadt path; fprintf fout "%s\n" line' | None ->
      (match parse_load_statement "loads" line with
      | Some (path,line') -> loads path; fprintf fout "%s\n" line' | None ->
      (match parse_load_statement "needs" line with
      | Some (path,line') -> needs path; fprintf fout "%s\n" line'
      | None -> fprintf fout "%s\n" line (* no linebreak needed! *))))
    lines;
  (* add digest *)
  let digest_str = Digest.file filename in
  let digest = Bytes.of_string digest_str in
  let the_str = ref "" in
  Bytes.iter (fun c ->
      let i = Char.code c in
      if !the_str = ""
      then the_str := string_of_int i
      else the_str := !the_str ^ "; " ^ (string_of_int i))
    digest;
  fprintf fout "(* update digest *)\n";
  fprintf fout "loaded_files := \n";
  fprintf fout "  let digest_bytes = [|%s|] in\n" !the_str;
  fprintf fout "  let digest = Bytes.init (Array.length digest_bytes) (fun i -> Char.chr digest_bytes.(i)) in\n";
  fprintf fout "  (\"%s\", Bytes.to_string digest)::!loaded_files;;\n\n" (Filename.basename filename);
  true;;

loadt filename;;

close_out fout;;
