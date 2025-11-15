type typ =
  | TyFun of { arg: typ; argname: string option; optional: bool; retty: typ }
  | TyApp of { args: typ list; destty: typ } (* string list, or (int, int) func *)
  | TyTuple of typ list
  | TyConst of string

let is_typevar (ty:typ): bool =
  match ty with
  | TyConst s -> String.starts_with ~prefix:"'" s
  | _ -> false

let rec get_fun_argtys (ty:typ): (typ * string option * bool) list =
  match ty with
  | TyFun x -> (x.arg, x.argname, x.optional) :: get_fun_argtys x.retty
  | _ -> []

let string_of_typ (t:typ): string =
  let wrap_paren_if b s = if b then "(" ^ s ^ ")" else s in
  let rec fn (needs_paren:bool) t: string =
    match t with
    | TyFun x ->
      wrap_paren_if needs_paren
       ((let sa = fn true x.arg in
         (match x.argname with
         | None -> ""
         | Some s -> (if x.optional then "?" else "") ^ s ^ ":") ^ sa) ^
        " -> " ^ fn false x.retty)
    | TyApp x ->
      wrap_paren_if needs_paren
       (let ss = String.concat "," (List.map (fn true) x.args) in
        let st = fn false x.destty in
        (wrap_paren_if (List.length x.args > 1) ss) ^ " " ^ st)
    | TyTuple x ->
      wrap_paren_if needs_paren (String.concat " * " (List.map (fn true) x))
    | TyConst s -> s
  in
  fn false t


open Parsetree

(* param_def is function_param (the OCaml compiler data structure).
   fun_arg_ty is the result of get_fun_argtys. Check whether these are consistent. *)
let check_param_consistency
    (param_def: function_param)
    (fun_arg_ty:typ * string option * bool)
    : bool =
  let _,lblname,is_optional = fun_arg_ty in
  match param_def.pparam_desc with
  | Pparam_val (lbl,exp0,p) ->
    (* P when lbl is Nolabel and exp0 is None
       ~l:P when lbl is Labelled l and exp0 is None
       ?l:P when lbl is Optional l and exp0 is None
       ?l:(P = E0) when lbl is Optional l and exp0 is Some E0 *)
   (match lbl with
    | Nolabel -> lblname = None && not is_optional
    | Labelled l -> lblname = Some l && not is_optional
    | Optional l -> lblname = Some l && is_optional)
  | Pparam_newtype _ ->
    (* We don't support this (yet). Just pass. *)
    true

(* Print the definition of a function parameter as a string, for description purpose *)
let function_param_to_str (args_info:function_param): string =
  let rec pat_to_str (pa:pattern_desc): string =
    match pa with
    | Ppat_var l -> l.txt
    | Ppat_tuple pl ->
      "(" ^ (String.concat "," (List.map (fun p -> pat_to_str p.ppat_desc) pl)) ^ ")"
    | _ -> "(unknown)" in

  match args_info.pparam_desc with
  | Pparam_val (lbl,exp0,p) ->
    (* According to doc:
      - P when lbl is Nolabel and exp0 is None
      - ~l:P when lbl is Labelled l and exp0 is None
      - ?l:P when lbl is Optional l and exp0 is None
      - ?l:(P = E0) when lbl is Optional l and exp0 is Some E0
    *)
   (match lbl with
    | Nolabel -> pat_to_str p.ppat_desc
    | Labelled l -> l ^ " (labeled)"
    | Optional l -> l ^ " (optional)")
  | _ -> "(don't know how to represent)"

(* Print the definition of a function parameter as a string, for description purpose *)
let function_param_to_str (arg_info:function_param): string =
  let rec pat_to_str (pa:pattern_desc): string =
    match pa with
    | Ppat_var l -> l.txt
    | Ppat_constraint (p,_) ->
      begin match p.ppat_desc with
      | Ppat_var l -> l.txt
      | _ -> "(unknown)"
      end
    | Ppat_tuple pl ->
      "(" ^ (String.concat "," (List.map (fun p -> pat_to_str p.ppat_desc) pl)) ^ ")"
    | _ -> "(unknown)" in

  match arg_info.pparam_desc with
  | Pparam_val (lbl,exp0,p) ->
    (* According to doc:
      - P when lbl is Nolabel and exp0 is None
      - ~l:P when lbl is Labelled l and exp0 is None
      - ?l:P when lbl is Optional l and exp0 is None
      - ?l:(P = E0) when lbl is Optional l and exp0 is Some E0
    *)
   (match lbl with
    | Nolabel -> pat_to_str p.ppat_desc
    | Labelled l -> l ^ " (labeled)"
    | Optional l -> l ^ " (optional)")
  | _ -> "(don't know how to represent)"

let get_function_param_name (arg_info:function_param): string option =
  match arg_info.pparam_desc with
  | Pparam_val (_,_,p) -> begin
    match p.ppat_desc with
    | Ppat_var l -> Some l.txt
    | Ppat_constraint (p,_) ->
      begin match p.ppat_desc with
      | Ppat_var l -> Some l.txt
      | _ -> None
      end
    | _ -> None
    end
  | _ -> None


(* Return an OCaml expression that evaluates to a string.
   The expression must work as a string printer *)
let rec get_stringifier (optional:bool) (ty:typ) (argname:string)
    : string =
  if optional then
    get_stringifier false (TyApp { args = [ty]; destty = TyConst "option" })
        argname
  else
    match ty with
    | TyConst "string" -> {|"\"" ^ (|} ^ argname ^ {|) ^ "\""|}
    | TyConst "int" -> "string_of_int " ^ argname
    | TyConst "term" -> {|"`" ^ (string_of_term |} ^ argname ^ {|) ^ "`"|}
    | TyConst "thm" ->
        (* Omit thm if too long *)
        "(let s = string_of_thm " ^ argname ^
        " in if String.length s > 1000 then \"(omitted thm)\" else s)"
    | TyTuple subtys ->
      let n = List.length subtys in
      let elemvars = List.init n (fun i -> "elem" ^ string_of_int i) in
      let strelem = List.map2 (get_stringifier false) subtys elemvars in
      "(let " ^ (String.concat "," elemvars) ^ " = " ^ argname ^ " in \n" ^
      {|"(" ^ |} ^ (String.concat " ^ \",\" ^ " (List.map (fun x -> "(" ^ x ^ ")") strelem)) ^
      {| ^ ")")|}
    | TyApp { args = [subty]; destty = TyConst "list" } ->
      {|"[" ^ (String.concat ", " (List.map (fun x -> "(" ^ |} ^
          (get_stringifier false subty "x") ^
          {| ^ ")") |} ^ argname ^ {|)) ^ "]"|}
    | TyApp { args = [subty]; destty = TyConst "option" } ->
      "(match (" ^ argname ^ ") with | None -> \"None\" | Some optval -> ("
        ^ (get_stringifier false subty "optval") ^ "))"
    | _ -> {|"(don't know how to express)"|}