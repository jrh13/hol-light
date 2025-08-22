(*
  Creates tactic wrappers and replaces the tactic users with the wrapper
  versions.

  This implementation assumes that OCaml 5.2 is used.
  https://ocaml.org/manual/5.2/api/compilerlibref/Parsetree.html
*)

(******************************************************************************
               Collect types from the interface file ( *.mli)
******************************************************************************)
open OcamlTypes

let parse_type (s:string): OcamlTypes.typ =
  let lexbuf = Lexing.from_string s in
  try
    Types_parser.typ_expr Types_lexer.token lexbuf
  with
  | Parsing.Parse_error ->
      let pos = Lexing.lexeme_start_p lexbuf in
      Printf.eprintf "Parse error at line %d, character %d\n"
        pos.pos_lnum (pos.pos_cnum - pos.pos_bol);
      exit 1
  | Types_lexer.LexError msg ->
      Printf.eprintf "Lexer error: %s\n" msg;
      exit 1

(* Type canonicalizer. Rewrites:
   - 'thm_tactic' to 'thm -> tactic'
   - '(..) -> goalstate' to 'tactic'
   - 'Hol_lib.x' to 'x'
*)
let rec canonicalize_type (ty:OcamlTypes.typ): OcamlTypes.typ =
  let is_asm_list_ty ty =
    OcamlTypes.is_typevar ty ||
    match ty with
    | TyApp { args = [t]; destty = TyConst "list" }
      when OcamlTypes.is_typevar t  -> true
    | TyApp { args = [TyTuple [TyConst "string"; TyConst "thm"]];
              destty = TyConst "list" }
      -> true
    | _ -> false
  in

  match ty with
  | TyFun x -> begin
    match x.arg, x.retty with
    | (TyTuple [inpty1; TyConst "term"], TyConst "goalstate")
      when is_asm_list_ty inpty1 -> TyConst "tactic"
    | _ ->
      let arg_canon = canonicalize_type x.arg and
          retty_canon = canonicalize_type x.retty in
      begin match arg_canon,retty_canon with
      | TyConst "term", TyConst "thm" ->
        (* Canonicalize 'term -> thm' to "conv". *)
        TyConst "conv"
      | _ -> TyFun { x with arg = arg_canon; retty = retty_canon }
      end
    end
  | TyApp x ->
    TyApp { x with args = List.map canonicalize_type x.args;
                   destty = canonicalize_type x.destty }
  | TyTuple x -> TyTuple (List.map canonicalize_type x)
  | TyConst s ->
    if s = "thm_tactic" then
      TyFun { arg = TyConst "thm"; argname = None; optional = false;
              retty = TyConst "tactic" }
    else if String.starts_with ~prefix:"Hol_lib." s then
      TyConst (String.sub s 8 (String.length s - 8))
    else TyConst s

let read_types (filename:string):(string, OcamlTypes.typ) Hashtbl.t =
  (* Note that a later definition overwrites a previous definition;
     let x:int = ...;;
     let x:string = ...;; (* This will overwrite the previous x *)
  *)
  let lines:string list = In_channel.with_open_text filename In_channel.input_lines in
  let tbl = Hashtbl.create 1024 in

  let prev_line = ref "" in
  let consume_line () =
    let l = !prev_line in
    prev_line := "";
    if not (String.starts_with ~prefix:"val " l) then () else
    match String.index_opt l ':' with
    | None -> failwith ("Unknown line: " ^ l)
    | Some idx ->
      let name = String.trim (String.sub l 4 (idx-4)) in
      let len = String.length l - idx - 1 in
      let ty = String.trim (String.sub l (idx+1) len) in
      let ty_expr = canonicalize_type (parse_type ty) in
      Hashtbl.add tbl name ty_expr
  in

  List.iter (fun line ->
    let line = String.trim line in
    let _ = if List.exists (fun p -> String.starts_with ~prefix:p line)
        ["val ";"type ";"module ";"exception ";"end\n"]
    then consume_line () in
    prev_line := !prev_line ^ line)
  lines;

  consume_line();

  tbl

let rec is_tactic_type ?(no_arg=false) (ty:OcamlTypes.typ): bool =
  match ty with
  | TyFun x -> if no_arg then false else is_tactic_type x.retty
  | TyConst "tactic" -> true
  | TyConst "Hol_lib.tactic" -> failwith "not canonicalized!"
  | _ -> false

let rec is_conv_type ?(no_arg=false) (ty:OcamlTypes.typ): bool =
  match ty with
  | TyFun { arg = TyConst "term"; retty = TyConst "thm" } ->
    failwith "not canonicalized!"
  | TyConst "conv" -> true
  | TyFun x -> if no_arg then false else is_conv_type x.retty
  | _ -> false


(******************************************************************************
                        Read marshalled AST
******************************************************************************)

open Parsetree

let string_of_location (loc:Location.t): string =
  let fbeg,lbeg,cbeg = Location.get_pos_info loc.loc_start in
  let fend,lend,cend = Location.get_pos_info loc.loc_end in
  Printf.sprintf "(%s,L%d,C%d ~ %s,L%d,C%d)" fbeg lbeg cbeg fend lend cend

let read_ast (filename:string): Parsetree.structure =
  let ic = open_in_bin filename in
  try
    (* AST_IMPL_MAGIC_NUMBER *)
    let magic = "Caml1999M034" in
    let magic_buffer = really_input_string ic (String.length magic) in
    if magic_buffer <> magic then
      failwith ("Does not have the magic string" ^ magic) else
    let loc_input_name = (input_value ic : string) in
    Printf.printf "read_ast: Location.input_name: %s\n" loc_input_name;
    Printf.printf "read_ast: Reading marshaled AST from %s\n\n" filename;
    Fun.protect ~finally: (fun () -> close_in ic)
      (fun () ->
        try
          let ast : Parsetree.structure = Marshal.from_channel ic in
          ast
        with
        | _ -> failwith "Error: Invalid marshaled AST format\n")
  with
  | Sys_error msg -> failwith (Printf.sprintf "Error: %s\n" msg)
  | End_of_file -> (close_in ic; failwith (Printf.sprintf "Error: Unexpected end of file\n"))


(******************************************************************************
                  Collect tactic & conversion definitions
******************************************************************************)


type hol_def_kind = KindTactic | KindConversion

type hol_def = {
  kind: hol_def_kind;
  ty: OcamlTypes.typ;
  arg_defs: function_param list;
  loc: Location.t
}

(* Skip these definitions returning tactic/conv type *)

let tactics_to_skip = [
  "then_";"thenl_";"then1_";"orelse_"
]

let convs_to_skip = [
  (* primitive inference rules as well as fns in fusion.ml *)
  "ASSUME";
  "BETA";
  "REFL";
  "new_axiom";
  "new_basic_definition";
  (* combinators *)
  "thenc_";
  "orelsec_";
  (* compute fns *)
  "WEAK_CBV_CONV";
  "CBV_CONV";
  (* other fns *)
  "apply_prover";
  "basic_prover";
  "define";
  "derive_nonschematic_inductive_relations";
  "instantiate_casewise_recursion";
  "new_definition";
  "new_inductive_definition";
  "new_recursive_definition";
  "new_specification";
  "prove_general_recursive_function_exists";
  "prove_inductive_relations_exist";
  "pure_prove_recursive_function_exists";
]

(* Collects tactic/conversion definitions and return their
   (type, argument names, (begin, end) location) in the file.
   Location.t already contains the range information. *)
let collect_defs
    (structure: Parsetree.structure)
    (types:(string, OcamlTypes.typ) Hashtbl.t)
    : (string, hol_def) Hashtbl.t =
  (* Note that a later definition overwrites a previous definition;
     let X_TAC:int->tactic = ...;;
     let X_TAC:string->tactic = ...;; (* This will overwrite the previous X_TAC *)
  *)
  let tbl = Hashtbl.create 1024 in
  let rec register (pd:pattern_desc) (arg_defs:function_param list)
                   (toplevel_loc:Location.t)
      : unit =
    match pd with
    | Ppat_var x ->
      let name = x.txt in
      if List.mem name tactics_to_skip then () else
      if List.mem name convs_to_skip then () else

      begin match Hashtbl.find_opt types name with
      | Some ty ->
        if is_tactic_type ty || is_conv_type ty then begin
          let k = if is_tactic_type ty then KindTactic else KindConversion in
         (if Hashtbl.mem tbl name then
            Hashtbl.replace tbl name {
              kind = k;
              ty = ty;
              arg_defs = arg_defs;
              loc = toplevel_loc
            }
          else
            Hashtbl.add tbl name {
              kind = k;
              ty = ty;
              arg_defs = arg_defs;
              loc = toplevel_loc
            });
          Printf.printf "Found %s definition %s:%s (loc:%s)\n"
            (if k = KindTactic then "tactic" else "conv")
            name (OcamlTypes.string_of_typ ty)
            (string_of_location toplevel_loc)
        end
      | None ->
        Printf.printf "(note: collect_defs: could not find %s from .mli)\n" name
      end
    | Ppat_tuple pats ->
      List.iter (fun p ->
          register p.ppat_desc arg_defs toplevel_loc)
        pats
    | Ppat_constraint (p,_) ->
      register p.ppat_desc arg_defs toplevel_loc
    | _ -> ()
  in

  (* Find the top-level let definitions *)
  List.iter (fun item ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) ->
          List.iter (fun (binding:value_binding) ->
              (* The tacticc/conversion name (keyword) *)
              let pat_desc:pattern_desc = binding.pvb_pat.ppat_desc in
              (* Tactic/conversion arguments. Interestingly, given
                 'let f x = ... in ...', the 'x' part appears at binding.pvb_expr. *)
              let args_info:function_param list =
                (* Deal with nested lets:
                   let my_tac a b =
                     let t = x in
                     fun (..) -> .. *)
                let rec get_let_expr_e2 (e:expression) =
                  match e.pexp_desc with
                  | Pexp_let (_,_,e) -> get_let_expr_e2 e
                  | _ -> e in
                (* Get additional arguments from 'let _ in fun add_args -> .. '. *)
                let rec collect_args (e:expression) =
                  let e = get_let_expr_e2 e in
                  match e.pexp_desc with
                  | Pexp_function (fnparams,_,fnbody) ->
                      fnparams @ (match fnbody with
                        | Pfunction_body e -> collect_args e
                        | _ -> [])
                  | _ -> [] in
                collect_args binding.pvb_expr in

              register pat_desc args_info item.pstr_loc)
            bindings
      | _ -> ())
    structure;
  tbl


(* An OCaml expression that explicitly uses tactic or conversion. *)
type user = {
  (* The name of tactic or conv.
     To figure out whether it is tactic or conv, consult def. *)
  name: string;
  (* The source code location of this entire expression *)
  expr_loc: Location.t;
  (* The source code location of this tactic keyword only *)
  tackey_loc: Location.t;
  (* The source code locations of the arguments *)
  arg_locs: Location.t list;
}

let print_user (tu:user) =
  Printf.printf "name of tactic or conv: %s\n" tu.name;
  Printf.printf "expr_loc: %s\n" (string_of_location tu.expr_loc);
  Printf.printf "tackey_loc: %s\n" (string_of_location tu.tackey_loc);
  Printf.printf "arg_locs: [\n";
  List.iter (fun loc -> Printf.printf "  %s\n" (string_of_location loc))
    tu.arg_locs;
  Printf.printf "]\n"

(* return true if l1's begin comes after l2's end. *)
let comes_after (l1:Location.t) (l2:Location.t): bool =
  let f1,l1l,l1c = Location.get_pos_info l1.loc_start in
  let f2,l2l,l2c = Location.get_pos_info l2.loc_end in
  assert (f1 = f2);
  l1l > l2l || (l1l = l2l && l1c > l2c)

let collect_users
    (structure: Parsetree.structure)
    (def_locs: (string, Location.t) Hashtbl.t)
    (def_types:(string, OcamlTypes.typ) Hashtbl.t)
    : user list =

  (* Remove scopes from the identifier l and pick the right one *)
  let find_tac_or_conv_name (l:Longident.t): string option =
    let s = match l with | Lident x -> Some x | Ldot (_,x) -> Some x | _ -> None in
    match s with
    | None -> None
    | Some x ->
      if Hashtbl.mem def_types x &&
        (let elem = Hashtbl.find def_types x in
          (is_tactic_type elem && not (List.mem x tactics_to_skip)) ||
          (is_conv_type elem && not (List.mem x convs_to_skip))) then
        Some x
      else None
  in

  let comes_after_def l0 (ndef:string) =
    match Hashtbl.find_opt def_locs ndef with
    | Some l -> comes_after l0 l
    | None ->
      (* the tactic or conversion 'ndef' defined in HOL Light kernel *)
      true
  in

  (* Traverse expressions and gather tactic/conversion users *)
  let res:user list ref = ref [] in
  let rec visit_expr (e: Parsetree.expression): unit =
    match e.pexp_desc with
    | Pexp_ident id ->
      begin match find_tac_or_conv_name id.txt with
      | Some n when comes_after_def id.loc n ->
        (* Only add to user if this tactic does not accept extra args *)
        let n_ty = Hashtbl.find def_types n in
        if is_tactic_type ~no_arg:true n_ty ||
           is_conv_type ~no_arg:true n_ty
        then
          let new_user:user = {
            name = n;
            expr_loc = e.pexp_loc;
            tackey_loc = e.pexp_loc;
            arg_locs = []
          } in
          res := new_user::!res
        else ()
      | _ -> ()
      end
    | Pexp_constant _ -> ()
    | Pexp_let (_, bindings, expr) ->
      List.iter visit_value_binding bindings;
      visit_expr expr
    | Pexp_function (_,_,fnbody) ->
      begin match fnbody with
      | Pfunction_body e -> visit_expr e
      | Pfunction_cases (cases,_,_) ->
        List.iter visit_case cases
      end
    | Pexp_apply (callee,args) ->
      (* The main case! *)
      begin match callee.pexp_desc with
      | Pexp_ident l ->
        begin match find_tac_or_conv_name l.txt with
        | Some n ->
          if comes_after_def l.loc n then
            let new_user = {
              name = n;
              expr_loc = e.pexp_loc;
              tackey_loc = callee.pexp_loc;
              arg_locs = List.map (fun (arg_label,argexpr) ->
                  (* TODO: deal with arg labels *)
                  argexpr.pexp_loc)
                args
            } in
            res := new_user::!res
        | None -> ()
        end
      | _ -> ()
      end;
      (* do not recursively visit callee! only visit the args *)
      List.iter (fun (_,argexpr) -> visit_expr argexpr) args
    | Pexp_match (expr, cases)
    | Pexp_try (expr, cases) ->
      visit_expr expr;
      List.iter (fun case -> visit_case case) cases
    | Pexp_tuple exprs ->
      List.iter (fun expr -> visit_expr expr) exprs
    | Pexp_construct (_, expropt)
    | Pexp_variant (_, expropt) ->
      Option.iter visit_expr expropt
    | Pexp_record (items,expropt) ->
      List.iter (fun (_, e) -> visit_expr e) items;
      Option.iter visit_expr expropt
    | Pexp_field (e, _) ->
      visit_expr e
    | Pexp_setfield (elhs, _, erhs) ->
      visit_expr elhs; visit_expr erhs
    | Pexp_array elist ->
      List.iter visit_expr elist
    | Pexp_ifthenelse (e1,e2,e3opt) ->
      visit_expr e1;
      visit_expr e2;
      Option.iter visit_expr e3opt
    | Pexp_sequence (e1,e2)
    | Pexp_while (e1,e2) ->
      visit_expr e1;
      visit_expr e2
    | Pexp_for (_,e1,e2,_,e3) ->
      visit_expr e1; visit_expr e2; visit_expr e3
    | Pexp_constraint (e,_)
    | Pexp_coerce (e,_,_)
    | Pexp_send (e,_) -> visit_expr e
    | Pexp_new _ -> ()
    | Pexp_setinstvar (_,e) -> visit_expr e
    | Pexp_override elist ->
      List.iter (fun (_,e) -> visit_expr e) elist
    | Pexp_letmodule (_,me,e) ->
      visit_module_expr me;
      visit_expr e
    | Pexp_letexception (_,e)
    | Pexp_assert e
    | Pexp_lazy e
    | Pexp_poly (e,_) -> visit_expr e
    | Pexp_object cs -> visit_class_structure cs
    | Pexp_newtype (_,e) -> visit_expr e
    | Pexp_pack me -> visit_module_expr me
    | Pexp_open (_,e) -> visit_expr e
    | Pexp_letop lo -> visit_letop lo
    | Pexp_extension _ -> failwith "Pexp_extension is unsupported"
    | Pexp_unreachable -> ()
  and visit_module_expr (me:Parsetree.module_expr): unit =
    failwith "module_expr is unsupported"
  and visit_class_structure (cs:Parsetree.class_structure): unit =
    failwith "class_structure is unsupported"
  and visit_letop (cs:Parsetree.letop): unit =
    failwith "letop is unsupported"
  and visit_value_binding (b:Parsetree.value_binding): unit =
    visit_expr b.pvb_expr
  and visit_case (c:Parsetree.case): unit =
    visit_expr c.pc_rhs
  in

  List.iter (fun item ->
      match item.pstr_desc with
      | Pstr_eval (e, _) -> visit_expr e
      | Pstr_value (_, bindings) ->
        List.iter visit_value_binding bindings
      | Pstr_primitive _ -> ()
      | Pstr_type _ -> ()
      | Pstr_typext _ -> ()
      | Pstr_exception _ -> ()
      | Pstr_module mb ->
        visit_module_expr mb.pmb_expr
      | Pstr_recmodule mblist ->
        List.iter (fun mb -> visit_module_expr mb.pmb_expr) mblist
      | Pstr_modtype _ -> failwith "Pstr_modtype is unsupported"
      | Pstr_open _ -> ()
      | Pstr_class _ -> failwith "Pstr_class is unsupported"
      | Pstr_class_type _ -> failwith "Pstr_class_type is unsupported"
      | Pstr_include _ -> ()
      | Pstr_attribute _ -> ()
      | Pstr_extension _ -> failwith "Pstr_extension is unsupported")
    structure;

  !res


(******************************************************************************
          Helper functions for locations and source code
******************************************************************************)

(* A special case when dealing with the HOL Light terms!
    For example, given a term
    `a = b /\
    c = d`,
    the preprocessor replaces the line breaks with a space:
    `a = b /\         c = d`
    ... making the column number after the closing '`' weird. *)
let adjust_position (linenum,colnum) (srclines:string array): int * int =
  let len = String.length srclines.(linenum - 1) in
  if len >= colnum then (linenum,colnum) (* no adjustment needed *) else
  let col_accml = ref len in
  let lcur = ref (linenum + 1) in
  let ans = ref (0,0) in
  while !col_accml <= colnum do
    let line = srclines.(!lcur - 1) in
    let len = String.length line in
    (if colnum < !col_accml + len then
      ans := (!lcur,colnum - !col_accml));
    lcur := 1 + !lcur;
    col_accml := len + !col_accml + 1(* the extra space preproc inserted *)
  done;
  !ans


(* A helper function for extracting source *)
let get_source (loc:Location.t) (srclines:string array): string =
  let _,lbeg,cbeg = Location.get_pos_info loc.loc_start in
  let _,lend,cend = Location.get_pos_info loc.loc_end in
  if lbeg > lend then
  failwith (Printf.sprintf "get_source: line number inversed! %d > %d" lbeg lend)
  else if (lbeg = lend) && (cbeg > cend) then
  failwith (Printf.sprintf "get_source: column number inversed! %d > %d" cbeg cend)
  else
   (let s = ref "" in
    let lend,cend = adjust_position (lend,cend) srclines in
    for lcur = lbeg to lend do
      let line = srclines.(lcur-1) in
      let ci = if lcur = lbeg then cbeg else 0 in
      let clen = (if lcur = lend then cend else String.length line) - ci in
      s := !s ^ String.sub line ci clen
    done;
    !s)

(* Build a line number mapping from the fully inlined input source code
   code to the original source codes

   arr[linenum(starting from 0)] = (linenum(starting from 1),file)

   This is kind of hacky and we can recompile the identical information by
   recompiling the source file with all line number directives preserved.
*)
let build_linemap (srclines:string array) input_ml_path: ((int * string) option) array =
  let match_linenum_dir (l:string): (int * string) option =
    if String.starts_with ~prefix:"#" l then try
    let i = String.index l ' ' in
      let len = String.length l in
      Some (int_of_string (String.sub l 1 (i-1)),
            String.sub l (i+2) (len-i-3) (* no quotes *))
    with _ -> None
    else None in

  let n = Array.length srclines in
  let arr = Array.make n None in
  let prevloc = ref (0,input_ml_path) in
  for i = 0 to n-1 do
    match match_linenum_dir srclines.(i) with
    | None ->
      let (lnum,file) = !prevloc in
       (arr.(i) <- Some (lnum,file);
        prevloc := (lnum+1,file))
    | Some (lnum,s) ->
     (arr.(i) <- None; (* line number dir itself does not originate from any file *)
      prevloc := (lnum,s))
  done;
  arr

(******************************************************************************
                         Generate tactic wrappers
******************************************************************************)

(* ast_path: the marshalled .bin file of .ml file containing tactic definitions
   interface_path: the path of .mli file containing type signatures of the
                   tactic definitions *)
let predefined_types: (string, OcamlTypes.typ) Hashtbl.t =
  let tbl = Hashtbl.create 16 in
  List.iter (fun (n,t) -> Hashtbl.add tbl n t)
    [
      "UNIFY_ACCEPT_TAC", parse_type "(term list) -> thm -> tactic"
    ];
  tbl

let rec takelist n (l:'a list) =
  if n = 0 then [] else
  match l with
  | [] -> []
  | h::t -> h::takelist (n-1) t

(* Returns (original tactic/conv definition location, tactic/conv name, new def) *)
let make_wrappers ast types (linenum_maps: ((int * string) option) array)
    :(Location.t * string * string) list =

  (*********************** Get tactic/conv definitions ************************)

  let definitions: (string, hol_def) Hashtbl.t =
      collect_defs ast types in

  (***** Generate wrapped tactics/conversions that generate proof trace *******)

  let wrappers:(Location.t * string * string) list ref = ref [] in

  (* Iterate over each tactic/conv definitions *)
  Hashtbl.iter (fun tname (def:hol_def) ->
      (*let typ,param_defs,loc = def.ty,def.arg_defs,def.loc in *)
      (* param_defs is the definitions of parameters of the original tactic/conv.
         Has type function_param. *)

      let tac_def_filepath,tac_def_line =
        let _,l,_ = Location.get_pos_info def.loc.loc_start in
        match linenum_maps.(l-1) with
        | None ->
          failwith (Printf.sprintf "No line number mapping from line %d? tactic name is %s\n" l tname)
        | Some (l,n) -> (n,l) in

      let s = ref ("let " ^ tname ^ " ?(args_str:string list option) ?(caller_linenum:(string * int) option)") in
      let argtys:(typ * string option * bool) list = get_fun_argtys def.ty in
      let numargs = List.length argtys in
      (* Cut away the extra argument, which can be:
        - (assumptions,goal) part for tactic
        - the input term for conv
        from parameters, if it exists. *)
      let arg_defs = takelist numargs def.arg_defs in
      let args = ref [(* arg ty, name, prefix string ("?", "~", "") *)] in

      (* Generate args *)
      let fresh_arg =
        let cnt = ref 0 in
        fun () ->
          let n = !cnt in
          cnt := n + 1;
          "arg" ^ (string_of_int n)
        in
      List.iteri (fun i (argty, argname_from_sig, optional) ->
          (* argname_from_sig is the labeled argument name appearing from the type signature *)

          (* Choose argname from argname_from_sig, arg_defs and fresh_arg *)
          let argname =
            if i < List.length arg_defs then begin
              (* The parameter definition is available! *)
              let arg_defs:function_param = List.nth arg_defs i in
              assert (check_param_consistency arg_defs (argty, argname_from_sig, optional));
              match argname_from_sig with
              | Some s -> s
              | None -> begin
                (* Try to get a name from arg_defs *)
                match get_function_param_name arg_defs with
                | Some s -> s
                | None -> fresh_arg ()
              end
            end else match argname_from_sig with
            | Some s -> s
            | None -> fresh_arg () in

          let sz = (
              let prefix =
                  if optional then "?" else
                  if argname_from_sig <> None then "~" else "" in
                args := !args @ [argty, argname, prefix];
                prefix ^ "(" ^ argname ^ ":" ^
              (let sty = string_of_typ argty in
               if optional then "(" ^ sty ^ ") option" else sty)
                ^ ")") in
          s := !s ^ " " ^ sz)
        argtys;

      match def.kind with
      | KindTactic -> begin
        s := !s ^ ": tactic =\n";

        (* Now the application part *)
        s := !s ^ "  fun (trace_asl,trace_g) ->\n";
        s := !s ^ "    let trace_goal_before = (trace_asl,trace_g) in\n";
        s := !s ^ "    let (trace_ga_inst,trace_goals_after,trace_justf) = " ^ tname;
        List.iter (fun (argty, argname, prefix) ->
            (* prefix is either "", "?" or "~" *)
            s := !s ^ " " ^ prefix ^ argname)
          !args;
        s := !s ^ " (trace_asl,trace_g) in\n";

        (* Add a record to ExportTrace *)
        s := !s ^ "    exptrace_add_tac \"" ^ tname ^ "\" {\n";
        s := !s ^ "      definition_line_number = (\"" ^ tac_def_filepath ^ "\","
                ^ (string_of_int tac_def_line) ^ ");\n";
        s := !s ^ "      user_line_number = (match caller_linenum with\n";
        s := !s ^ "          | None -> (\"\",0)\n";
        s := !s ^ "          | Some t -> t\n";
        s := !s ^ "        );\n";
        s := !s ^ "      goal_before = trace_goal_before;\n";
        s := !s ^ "      goals_after = trace_goals_after;\n";
        s := !s ^ "      num_subgoals = List.length trace_goals_after;\n";
        s := !s ^ "    } (fun () -> {\n";

        s := !s ^ "      names = to_n_elems [" ^
          String.concat "; " (List.map
            (fun pdef -> "\"" ^ function_param_to_str pdef ^ "\"")
            arg_defs) ^ "] " ^ (string_of_int numargs) ^ ";\n";
        s := !s ^ "      types = [" ^
          String.concat "; " (List.map
            (fun (argty,_,_) -> "\"" ^ string_of_typ argty ^ "\"") argtys) ^
          "];\n";
        (if numargs = 0 then
        s := !s ^ "      values = [];\n"
        else (
        s := !s ^ "      values = [\n";
        s := !s ^ "        " ^
          (String.concat ";\n        "
            (List.map (fun (argty, argname, prefix) ->
              OcamlTypes.get_stringifier (prefix = "?") argty argname) !args)) ^ "\n";
        s := !s ^ "      ];\n"
        ));
        s := !s ^ "      exprs = to_n_elems\n";
        s := !s ^ "         (match args_str with | Some s -> s  | None -> [])\n";
        s := !s ^ "         " ^ (string_of_int numargs) ^ ";\n";
        s := !s ^ "    });\n";

        s := !s ^ "    (trace_ga_inst,trace_goals_after,trace_justf)\n";

        wrappers := (def.loc,tname,!s)::!wrappers
      end
      | KindConversion -> begin
        s := !s ^ ": conv =\n";

        (* Now the application part *)
        s := !s ^ "  fun (t_input:term) ->\n";
        s := !s ^ "    let thm_output = " ^ tname;
        List.iter (fun (argty, argname, prefix) ->
            (* prefix is either "", "?" or "~" *)
            s := !s ^ " " ^ prefix ^ argname)
          !args;
        s := !s ^ " t_input in\n";

        (* Add a record to ExportTrace *)
        s := !s ^ "    exptrace_add_conv \"" ^ tname ^ "\" {\n";
        s := !s ^ "      definition_line_number = (\"" ^ tac_def_filepath ^ "\","
                ^ (string_of_int tac_def_line) ^ ");\n";
        s := !s ^ "      user_line_number = (match caller_linenum with\n";
        s := !s ^ "          | None -> (\"\",0)\n";
        s := !s ^ "          | Some t -> t\n";
        s := !s ^ "        );\n";
        s := !s ^ "      input = t_input;\n";
        s := !s ^ "      output = thm_output;\n";
        s := !s ^ "    } (fun () -> {\n";

        s := !s ^ "      names = to_n_elems [" ^
          String.concat "; " (List.map
            (fun pdef -> "\"" ^ function_param_to_str pdef ^ "\"")
            arg_defs) ^ "] " ^ (string_of_int numargs) ^ ";\n";
        s := !s ^ "      types = [" ^
          String.concat "; " (List.map
            (fun (argty,_,_) -> "\"" ^ string_of_typ argty ^ "\"") argtys) ^
          "];\n";
        (if numargs = 0 then
        s := !s ^ "      values = [];\n"
        else (
        s := !s ^ "      values = [\n";
        s := !s ^ "        " ^
          (String.concat ";\n        "
            (List.map (fun (argty, argname, prefix) ->
              OcamlTypes.get_stringifier (prefix = "?") argty argname) !args)) ^ "\n";
        s := !s ^ "      ];\n"
        ));
        s := !s ^ "      exprs = to_n_elems\n";
        s := !s ^ "         (match args_str with | Some s -> s  | None -> [])\n";
        s := !s ^ "         " ^ (string_of_int numargs) ^ ";\n";
        s := !s ^ "    });\n";

        s := !s ^ "    thm_output\n";

        wrappers := (def.loc,tname,!s)::!wrappers

      end
      )
    definitions;

  !wrappers

let print_wrappers ml_path ast_path interface_path out_path =
  let srclines:string array = Array.of_list
      (In_channel.with_open_text ml_path In_channel.input_lines) in
  let linenum_maps = build_linemap srclines ml_path in

  let ast = read_ast ast_path in
  let types:(string, OcamlTypes.typ) Hashtbl.t = read_types interface_path in
  let res = make_wrappers ast types linenum_maps in
  let res = List.sort (fun (_,n,_) (_,n2,_) -> compare n n2) res in
  let f = open_out out_path in
  List.iter (fun (_,_,def) -> Printf.fprintf f "%s;;\n" def) res;
  close_out f


(******************************************************************************
                       Modify a proof file
******************************************************************************)

(* ml_path: path to the proof .ml file
   ast_path: the marshalled .bin file of .ml file containing tactics/conversions
   interface_path: the path of .mli file containing type signatures of the
                   tactics/conversions *)
let modify ml_path ast_path interface_path kernel_interface_path output_path =
  (* Combine declarations from two .mlis and build one typ decls *)
  let types:(string, OcamlTypes.typ) Hashtbl.t = read_types kernel_interface_path in
  let types':(string, OcamlTypes.typ) Hashtbl.t = read_types interface_path in
  Hashtbl.iter (fun k v ->
      if Hashtbl.mem types k then Hashtbl.replace types k v
      else Hashtbl.add types k v)
    types';

  let srclines:string array = Array.of_list
      (In_channel.with_open_text ml_path In_channel.input_lines) in
  let linenum_maps = build_linemap srclines ml_path in
  let ast = read_ast ast_path in

  (* New tactic/conversion definitions *)
  (* Insert after, new definition *)
  let wrappers = make_wrappers ast types linenum_maps in
  let tac_wrapper_inserters:(Lexing.position * string) list =
      List.map (fun ((x:Location.t),_,y) ->
        (* The location of structure item does not include the last ';;'
           separator! *)
        (x.loc_end,";;\n" ^ y))
      wrappers in
  let def_locations:(string, Location.t) Hashtbl.t = Hashtbl.create 128 in
  List.iter (fun (loc,name,_) ->
      Hashtbl.add def_locations name loc)
    wrappers;

  (* Add args to tactic users *)
  let tac_users:user list = collect_users ast def_locations types in
  let tac_users_inserters:(Lexing.position * string) list = List.flatten
    (List.map
      (fun tu ->
        let opening_paren_pos = tu.expr_loc.loc_start in
        let closing_paren_pos = tu.expr_loc.loc_end in
        let caller_linenum_info =
          let _,l,_ = Location.get_pos_info opening_paren_pos in
          let op = linenum_maps.(l-1) in
          match op with
          | None ->
            failwith (Printf.sprintf "No line number mapping at %s from line %d\n" ml_path l)
          | Some (l,s) ->
            "(\"" ^ s ^ "\", " ^ (string_of_int l) ^ ")" in

        if tu.arg_locs = [] then
          [(opening_paren_pos,"(");
           (closing_paren_pos, " ~caller_linenum:" ^ caller_linenum_info ^
                               " ~args_str:[])")]

        else begin
          let insert_after = tu.tackey_loc.loc_end in
          let arg = ref (" ~caller_linenum:" ^ caller_linenum_info) in
          arg := !arg ^ " ~args_str:[";
          arg := !arg ^ (String.concat "; " (List.map
              (fun loc ->
                let argstr = String.escaped (get_source loc srclines) in
                "\"" ^ argstr ^ "\"")
              tu.arg_locs)) ^ "]";

          [(insert_after, !arg ^ " ")]
        end)
      tac_users) in

  (* Now merge the 'updates' and sort by their insertion points
     (in decreasing order) *)
  let inserters = tac_wrapper_inserters @ tac_users_inserters in
  let loc_comp ((loc1,_):Lexing.position*string) ((loc2,_):Lexing.position*string): int =
    let f1,l1,c1 = Location.get_pos_info loc1 in
    let f2,l2,c2 = Location.get_pos_info loc2 in
    assert (f1 = f2);
    if l1 != l2 then l2 - l1 else c2 - c1 in
  let inserters = List.sort loc_comp inserters in

  let inserters = List.map (fun (loc,str) ->
      let _,l,c = Location.get_pos_info loc in
      (adjust_position (l,c) srclines, str))
    inserters in

  List.iter (fun ((l,c),contents) ->
      let s = srclines.(l-1) in
      let slen = String.length s in
      let sbef, safter = String.sub s 0 c, String.sub s c (slen-c) in
      srclines.(l-1) <- sbef ^ contents ^ safter
  ) inserters;

  (* Emit the result to a file! *)
  let f = open_out output_path in
  Array.iter (fun l -> Printf.fprintf f "%s\n" l) srclines;
  close_out f

(******************************************************************************
              Collect top-level theorems ('let .. = prove(...)')
******************************************************************************)

(* ml_path: path to the proof .ml file
   ast_path: the marshalled .bin file of .ml file containing tactics/conversions
*)
let collect_toplevel_thms ast_path output_path =
  let ast = read_ast ast_path in

  let thms:
    (structure_item (* top-level item *)
     * string (* theorem name *)
     * expression (* goal *)
     * expression (* tactic *)) list ref
    = ref [] in

  let is_ident (e:expression) (ident:string) =
    match e.pexp_desc with
    | Pexp_ident { txt = Lident x ; _ } ->
      x = ident
    | _ -> false in

  (* Find the top-level let definitions of the form
     'let _ = prove(_,_);;' or
     'let _ = time prove(_,_);;' *)
  List.iter (fun (item:structure_item) ->
      match item.pstr_desc with
      | Pstr_value (_, bindings) ->
          List.iter (fun (binding:value_binding) ->
              (* binding is: 'pattern = expr' *)
              (* The theorem name *)
              let pat_desc:pattern_desc = binding.pvb_pat.ppat_desc in
              match pat_desc with
              | Ppat_var (idloc: string Asttypes.loc) -> begin
                (* The right hand side. It must be 'prove(a,b)'. *)
                match binding.pvb_expr.pexp_desc with
                (* prove(_,_) *)
                | Pexp_apply (prove_fn, [Nolabel,prove_args])
                    when is_ident prove_fn "prove" -> begin
                  match prove_args.pexp_desc with
                  | Pexp_tuple [goal_term;proof_term] ->
                    (* Found it! :) *)
                    thms := (item, idloc.txt, goal_term, proof_term)::!thms
                  | _ -> ()
                  end

                (* time prove(_,_) *)
                | Pexp_apply (time_fn, [Nolabel,prove_fn; Nolabel,prove_args])
                    when is_ident time_fn "time" && is_ident prove_fn "prove" -> begin
                  match prove_args.pexp_desc with
                  | Pexp_tuple [goal_term;proof_term] ->
                    (* Found it! :) *)
                    thms := (item, idloc.txt, goal_term, proof_term)::!thms
                  | _ -> ()
                  end
                | _ -> () 
                end
              | _ -> ())
            bindings
      | _ -> ())
    ast;

  (* Emit the result to a file! *)
  let f = open_out output_path in
  let len = List.length !thms in
  Printf.fprintf f "[\n";
  List.iteri (fun idx (struct_itm, thmname, goal_term, proof_term) ->
      let open Location in
      let filename,linenum_start,_ = get_pos_info struct_itm.pstr_loc.loc_start in
      let _,goal_linenum_start,goal_colnum_start = get_pos_info goal_term.pexp_loc.loc_start in
      let _,goal_linenum_end,goal_colnum_end     = get_pos_info goal_term.pexp_loc.loc_end in
      let _,proof_linenum_start,proof_colnum_start = get_pos_info proof_term.pexp_loc.loc_start in
      let _,proof_linenum_end,proof_colnum_end     = get_pos_info proof_term.pexp_loc.loc_end in

      Printf.fprintf f "  {\n";
      Printf.fprintf f "    \"theorem_name\":\"%s\",\n" thmname;
      Printf.fprintf f "    \"filename\":\"%s\",\n" filename;
      Printf.fprintf f "    \"toplevel_theorem_linenum_start\":%d,\n" linenum_start;
      Printf.fprintf f "    \"goal_linenum_start\":\"%d\",\n" goal_linenum_start;
      Printf.fprintf f "    \"goal_colnum_start\":\"%d\",\n"  goal_colnum_start;
      Printf.fprintf f "    \"goal_linenum_end\":\"%d\",\n"   goal_linenum_end;
      Printf.fprintf f "    \"goal_colnum_end\":\"%d\",\n"    goal_colnum_end;
      Printf.fprintf f "    \"proof_linenum_start\":\"%d\",\n" proof_linenum_start;
      Printf.fprintf f "    \"proof_colnum_start\":\"%d\",\n"  proof_colnum_start;
      Printf.fprintf f "    \"proof_linenum_end\":\"%d\",\n"   proof_linenum_end;
      Printf.fprintf f "    \"proof_colnum_end\":\"%d\"\n"     proof_colnum_end;
      Printf.fprintf f "  }%s\n" (if idx + 1 = len then "" else ",")
    )
    (List.rev !thms);
  Printf.fprintf f "]\n"


let () =
  let print_help () = begin
    Printf.printf "Usage: %s make-wrappers <input .ml file, inlined> <marshaled_ast_file (output of get-ast.sh)> <.mli file (output of get-ast.sh)> <save to>\n" Sys.argv.(0);
    Printf.printf "Usage: %s modify <input .ml file, inlined> <marshaled_ast_file (output of get-ast.sh)> <.mli file (output of get-ast.sh)> <kernel.mli> <save to>\n"
        Sys.argv.(0);
    Printf.printf "Usage: %s collect-toplevel-thms <marshaled_ast_file (output of get-ast.sh)> <save to>\n" Sys.argv.(0)
  end in
  if Array.length Sys.argv < 4 then begin
    print_help ();
    exit 1
  end;
  match Sys.argv.(1) with
  | "make-wrappers" ->
    if Array.length Sys.argv = 6 then
      print_wrappers (Sys.argv.(2)) (Sys.argv.(3)) (Sys.argv.(4)) (Sys.argv.(5))
    else print_help()
  | "modify" ->
    if Array.length Sys.argv = 7 then
      modify (Sys.argv.(2)) (Sys.argv.(3)) (Sys.argv.(4)) (Sys.argv.(5)) (Sys.argv.(6))
    else print_help()
  | "collect-toplevel-thms" ->
    if Array.length Sys.argv = 4 then
      collect_toplevel_thms (Sys.argv.(2)) (Sys.argv.(3))
    else print_help()
  | _ -> (print_help(); failwith "Unknown option")

