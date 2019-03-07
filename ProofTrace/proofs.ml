(* ========================================================================= *)
(* Tooling for the generation of the ProofTrace dataset.                     *)
(* ========================================================================= *)

#load "unix.cma";;
#load "str.cma";;

(* ------------------------------------------------------------------------- *)
(* Marshalling of term to AST-like.                                          *)
(* ------------------------------------------------------------------------- *)

let type_string ty =
  let rec args_str args =
    match args with
      [] -> ""
    | ty::tail -> Printf.sprintf "[%s]%s"
                                 (type_str ty) (args_str tail)
  and type_str ty =
    match ty with
      Tyvar(v) -> Printf.sprintf "v[%s]"
                                 (String.escaped v)
    | Tyapp(c,args) -> Printf.sprintf "c[%s][%s]"
                                      (String.escaped c) (args_str args)
  in (type_str ty)

let rec term_string tm =
  match tm with
    Var(v,ty) -> Printf.sprintf "v(%s)(%s)"
                                (String.escaped v) (type_string ty)
  | Const(c,ty) -> Printf.sprintf "c(%s)(%s)"
                                  (String.escaped c) (type_string ty)
  | Comb(t1,t2) -> Printf.sprintf "C(%s)(%s)"
                                  (term_string t1) (term_string t2)
  | Abs(t1,t2) -> Printf.sprintf "A(%s)(%s)"
                                 (term_string t1) (term_string t2)

(* ------------------------------------------------------------------------- *)
(* Marshalling of proof to JSON parts.                                       *)
(* ------------------------------------------------------------------------- *)

let rec inst_string insts =
  match insts with
    [] -> ""
  | (t1,t2)::[] -> Printf.sprintf "[\"%s\", \"%s\"]"
                                  (term_string t2)
                                  (term_string t1)
  | (t1,t2)::tail -> Printf.sprintf "[\"%s\", \"%s\"], %s"
                                    (term_string t2)
                                    (term_string t1)
                                    (inst_string tail)

let rec instt_string insts =
  match insts with
    [] -> ""
  | (t1,t2)::[] -> Printf.sprintf "[\"%s\", \"%s\"]"
                                  (type_string t2)
                                  (type_string t1)
  | (t1,t2)::tail -> Printf.sprintf "[\"%s\", \"%s\"], %s"
                                    (type_string t2)
                                    (type_string t1)
                                    (instt_string tail)

let proof_index proof =
  let Proof(idx,_,_) = proof in idx

let proof_content_string content =
  match content with
    Prefl(tm) -> Printf.sprintf "[\"REFL\", \"%s\"]"
                                (term_string tm)
  | Ptrans(p1,p2) -> Printf.sprintf "[\"TRANS\", %d, %d]"
                                    (proof_index p1)
                                    (proof_index p2)
  | Pmkcomb(p1,p2) -> Printf.sprintf "[\"MK_COMB\", %d, %d]"
                                     (proof_index p1)
                                     (proof_index p2)
  | Pabs(p1,tm) -> Printf.sprintf "[\"ABS\", %d, \"%s\"]"
                                  (proof_index p1)
                                  (term_string tm)
  | Pbeta(tm) -> Printf.sprintf "[\"BETA\", \"%s\"]"
                                (term_string tm)
  | Passume(tm) -> Printf.sprintf "[\"ASSUME\", \"%s\"]"
                                  (term_string tm)
  | Peqmp(p1,p2) -> Printf.sprintf "[\"EQ_MP\", %d, %d]"
                                   (proof_index p1)
                                   (proof_index p2)
  | Pdeduct(p1,p2) -> Printf.sprintf "[\"DEDUCT_ANTISYM_RULE\", %d, %d]"
                                     (proof_index p1)
                                     (proof_index p2)
  | Pinst(p1,insts) -> Printf.sprintf "[\"INST\", %d, [%s]]"
                                      (proof_index p1)
                                      (inst_string insts)
  | Pinstt(p1,insts) -> Printf.sprintf "[\"INST_TYPE\", %d, [%s]]"
                                       (proof_index p1)
                                       (instt_string insts)
  | Paxiom(tm) -> Printf.sprintf "[\"AXIOM\", \"%s\"]"
                                 (term_string tm)
  | Pdef(tm,name,ty) -> Printf.sprintf "[\"DEFINITION\", \"%s\", \"%s\"]"
                                       (term_string tm)
                                       (String.escaped name)
  | Pdeft(p1,tm,name,ty) -> Printf.sprintf
                              "[\"TYPE_DEFINITION\", %d, \"%s\", \"%s\"]"
                              (proof_index p1)
                              (term_string tm)
                              (String.escaped name)


let proof_string proof =
  let Proof(idx,thm,content) = proof in
  Printf.sprintf "{\"id\": %d, \"pr\": %s}"
                 idx
                 (proof_content_string content);;

(* ------------------------------------------------------------------------- *)
(* Marshalling of thm to JSON.                                               *)
(* ------------------------------------------------------------------------- *)

let thm_string th =
  let asl,tm = dest_thm th in
  let rec asl_string asl =
    match asl with
      [] -> ""
    | tm::[] -> Printf.sprintf "\"%s\"" (term_string tm)
    | tm::tail -> Printf.sprintf "\"%s\", %s"
                                 (term_string tm)
                                 (asl_string tail)
  in Printf.sprintf "{\"hy\": [%s], \"cc\": \"%s\"}"
                    (asl_string asl)
                    (term_string tm)

let theorem_string proof =
  let Proof(idx,thm,content) = proof in
  Printf.sprintf "{\"id\": %d, \"th\": %s}"
                 idx
                 (thm_string thm);;


(* ------------------------------------------------------------------------- *)
(* Proofs and Theorems trace dumping.                                        *)
(* ------------------------------------------------------------------------- *)

let dump_proofs filename =
  let foutc = open_out filename in
  (do_list (fun p -> Printf.fprintf foutc
                                    "%s\n"
                                    (proof_string p)) (proofs());
   flush foutc;
   close_out foutc)
;;

let dump_theorems filename =
  let foutc = open_out filename in
  (do_list (fun p -> Printf.fprintf foutc
                     "%s\n"
                     (theorem_string p)) (proofs());
   flush foutc;
   close_out foutc)
;;

(* ------------------------------------------------------------------------- *)
(* Theorem names extraction (inspired by HolStep, but non-destructive).      *)
(* ------------------------------------------------------------------------- *)

let PROVE_1_RE = Str.regexp (String.concat "" (
  "\\(let\\|and\\)[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*"::
  "=[ \n\t]*"::
  "\\(prove\\|"::
  "prove_by_refinement\\|"::
  "new_definition\\|"::
  "new_basic_definition\\|"::
  "new_axiom\\|"::
  "new_infix_definition\\|"::
  "INT_OF_REAL_THM\\|"::
  "define_finite_type\\|"::
  "TAUT\\|"::
  "INT_ARITH\\|"::
  "new_recursive_definition\\)"::
  []
))

let PROVE_2_RE = Str.regexp (String.concat "" (
  "\\(let\\|and\\)[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*"::
  "=[ \n\t]*"::
  "\\(define_type\\|"::
  "(CONJ_PAIR o prove)\\)"::
  []
))

let PROVE_3_RE = Str.regexp (String.concat "" (
  "\\(let\\|and\\)[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*,[ \n\t]*"::
  "\\([a-zA-Z0-9_-]+\\)[ \n\t]*"::
  "=[ \n\t]*"::
  "\\(new_inductive_definition\\)"::
  []
))

let source_files() =
  let select str = Str.string_match (Str.regexp ".*\\.[hm]l$") str 0 in
  let rec walk acc = function
  | [] -> (acc)
  | dir::tail ->
      let contents = Array.to_list (Sys.readdir dir) in
      let contents = List.rev_map (Filename.concat dir) contents in
      let dirs, files =
        List.fold_left (fun (dirs,files) f ->
                          match Sys.is_directory f with
                          | false -> (dirs, f::files)  (* Regular file *)
                          | true -> (f::dirs, files)  (* Directory *)
        ) ([],[]) contents in
      let matched = List.filter (select) files in
        walk (matched @ acc) (dirs @ tail)
  in walk [] [Sys.getcwd()]
;;

let load_file f =
  let ic = open_in f in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (s)

let extract_prove_1 f =
  let content = Bytes.to_string(load_file f) in
  let rec search acc start =
    try
      let _ = Str.search_forward PROVE_1_RE content start in
      let matches = (Str.matched_group 2 content)::[] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let extract_prove_2 f =
  let content = Bytes.to_string(load_file f) in
  let rec search acc start =
    try
      let _ = Str.search_forward PROVE_2_RE content start in
      let matches = (Str.matched_group 2 content)::
                    (Str.matched_group 3 content)::
                    [] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

let extract_prove_3 f =
  let content = Bytes.to_string(load_file f) in
  let rec search acc start =
    try
      let _ = Str.search_forward PROVE_3_RE content start in
      let matches = (Str.matched_group 2 content)::
                    (Str.matched_group 3 content)::
                    (Str.matched_group 4 content)::
                    [] in
      search (matches @ acc) (Str.match_end())
    with e -> (acc)
  in search [] 0
;;

(* ------------------------------------------------------------------------- *)
(* Names trace dumping (:see_no_evil)                                        *)
(* ------------------------------------------------------------------------- *)

let eval code =
  let as_buf = Lexing.from_string code in
  let parsed = !Toploop.parse_toplevel_phrase as_buf in
  ignore (Toploop.execute_phrase true Format.std_formatter parsed)

let _CODE_GEN name = Printf.sprintf
                       "_IDX := proof_index (proof_of %s);;"
                       name
let _IDX = ref (0)

let dump_names filename =
  let foutc = open_out filename in
  let acc = ref ([]) in
  (do_list (fun f -> acc := !acc @
                     (extract_prove_1 f) @
                     (extract_prove_2 f) @
                     (extract_prove_3 f)) (source_files());
   acc := List.sort_uniq compare !acc;
   do_list (fun name ->
               try
                 eval (_CODE_GEN name);
                 Printf.fprintf foutc
                                "{\"id\": %d, \"nm\": \"%s\"}\n"
                                !_IDX name;
               with _ -> ()
            ) (!acc);
   flush foutc;
   close_out foutc)
;;
