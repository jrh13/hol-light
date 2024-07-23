(* This is an implementation of the pretty printer from L.C. Paulson's
   ML for the working programmer. The printer has been extended to support
   different kinds of 'blocks' with behavior that correspond to those supported
   by the OCaml Format library:

   - Within a (horizontal) hblock, break hints never split the line,
   - within a (vertical) vblock, break hints always split the line,
   - within a (horizontal/vertical) hvblock, break hints split the line when
     the block does not fit on the current line,
   - within a compacting block (the standard block), a break hint never splits
     the line unless there is no more space on the current line.

   (I think the blocks are slightly broken at the moment.)
 *)

module App_list = struct

  let append l r =
    match l, r with
    | _, Nil -> l
    | Nil, _ -> r
    | _, _ -> Append (l, r) ;;

  let list = function
    | [] -> Nil
    | xs -> List xs ;;

  let empty = Nil;;

  let rec map f l =
    match l with
    | Nil -> Nil
    | List xs -> List (List.map f xs)
    | Append (l, r) -> Append (map f l, map f r) ;;

  let rec iter f l =
    match l with
    | Nil -> ()
    | List xs -> List.app f xs
    | Append (l, r) ->
        iter f l;
        iter f r
  ;;

  let rec to_list l =
    match l with
    | Nil -> []
    | List xs -> xs
    | Append (l, r) -> to_list l @ to_list r ;;

  let rec concat_aux sofar l =
    match l with
    | Nil -> sofar
    | List xs -> String.concat xs :: sofar
    | Append (l, r) -> concat_aux (concat_aux sofar r) l ;;

  let concat l = String.concat (concat_aux [] l) ;;

end;; (* struct *)

module Pretty_core = struct

  type block_type =
    | Horizontal
    | Vertical
    | Horizontal_vertical
    | Compacting
  ;;

  type token =
      | Block of block_type * token list * int * int
      | String of string
      | Break of int * int
      | Newline
  ;;

  let rec breakdist after = function
    | [] -> after
    | t :: es ->
        match t with
        | Block (_, _, _, len) -> len + breakdist after es
        | String s -> String.size s + breakdist after es
        | Break _ | Newline -> 0
  ;;

  let print margin tok =
    let space = ref margin in
    let blanks n =
      space := !space - n;
      App_list.list (List.tabulate n (fun _ -> " ")) in
    let newline () =
      space := margin;
      App_list.list ["\n"] in
    let break_line offset width =
      let out1 = newline () in
      let out2 = blanks (offset + margin - width) in
      App_list.append out1 out2 in
    let rec printing block_type blockspace after toks =
      match toks with
      | [] -> App_list.empty
      | tok::es ->
          let out1 =
            match tok with
            | Block (typ, bes, indent, len) ->
                printing typ (!space - indent) (breakdist after es) bes
            | String s ->
                space := !space - String.size s;
                App_list.list [s]
            | Break (len, offset) -> (* Depends on the block type: *)
                begin
                  match block_type with
                  (* Never split the line at this level *)
                  | Horizontal -> blanks len
                  (* Always split the line at this level *)
                  | Vertical -> break_line offset blockspace
                  (* Behavior depends on width *)
                  | Compacting (* TODO: Not faithful to format.ml *)
                  | Horizontal_vertical ->
                      if len + breakdist after es <= !space
                      then blanks len
                      else break_line offset blockspace
                end
            | Newline -> newline () in
          let out2 = printing block_type blockspace after es in
          App_list.append out1 out2 in
    printing Compacting margin 0 [tok]
  ;;

  let string s = String s
  ;;

  let break l i = Break (l, i)
  ;;

  let space = Break (1, 0)
  ;;

  let newline = Newline
  ;;

  let mk_block =
    let length =
      function
      | Block (_, _, _, len) -> len
      | String s -> String.size s
      | Break (len, _) -> len
      | Newline -> 0 in
    let sum = List.foldl (fun t s -> s + length t) 0 in
    fun typ indent toks -> Block (typ, toks, indent, sum toks)
  ;;

  let mk_block typ indent toks =
    mk_block typ indent toks;;

  let block = mk_block Compacting
  ;;

  let hblock = mk_block Horizontal 0
  ;;

  let vblock = mk_block Vertical
  ;;

  let hvblock = mk_block Horizontal_vertical
  ;;

end;; (* struct *)

module Pretty_imp = struct

  type block_type =
    | H_block
    | V_block
    | Hv_block
    | C_block
  ;;

  type token_queue =
    Token_queue of Pretty_core.token list *   (* stack of tokens *)
                   int                    *   (* block indent    *)
                   block_type                 (* block type      *)
  ;;

  let tq_empty ind typ = Token_queue ([], ind, typ)
  ;;

  let tq_enqueue (Token_queue (ts, ind, typ)) tok =
    Token_queue (tok::ts, ind, typ)
  ;;

  let tq_to_block (Token_queue (ts, ind, typ)) =
    match typ with
    | H_block -> Pretty_core.hblock (List.rev ts)
    | Hv_block -> Pretty_core.hvblock ind (List.rev ts)
    | V_block -> Pretty_core.vblock ind (List.rev ts)
    | C_block -> Pretty_core.block ind (List.rev ts)
  ;;

  type state =
    St of token_queue list ref (* intermediate result *)
  ;;

  let st_insert (St qs) tok =
    match !qs with
    | [] ->
        qs := [tq_enqueue (tq_empty 0 C_block) tok]
    | tq::tqs ->
        qs := tq_enqueue tq tok :: tqs
  ;;

  let st_remove (St qs) =
    match !qs with
    | [] -> failwith ("Pretty_imp.close_block: " ^
                      "Impossible: empty token_queue stack in state!")
    | tq::tqs ->
        qs := tqs;
        tq
  ;;

  let print_string st str = st_insert st (Pretty_core.string str)
  ;;

  let print_break st l i = st_insert st (Pretty_core.break l i)
  ;;

  let print_space st = st_insert st Pretty_core.space
  ;;

  let new_block (St st) indent typ =
    st := tq_empty indent typ :: !st

  let open_block st indent = new_block st indent C_block
  ;;

  let open_hblock st = new_block st 0 H_block
  ;;

  let open_hvblock st indent = new_block st indent Hv_block
  ;;

  let open_vblock st indent = new_block st indent V_block
  ;;

  let close_block st =
    let tq = st_remove st in
    let tok = tq_to_block tq in
    st_insert st tok
  ;;


  let is_done (St st) =
    match !st with
    | [Token_queue ([tok], _, _)] -> true
    | _ -> false

  (* OA: Removed st_flush because its a no-op in this code.
     print_newline simply prints the newline character.
   *)

  let print_newline st =
    st_insert st Pretty_core.newline
  ;;

  let empty () : state =
    let st = St (ref [tq_empty 0 C_block]) in
    open_block st; st
  ;;

  let to_token (St st) =
    close_block (St st);
    match !st with
    | [Token_queue ([tok], _, _)] -> tok
    | [Token_queue ([], _, _)] -> failwith "Pretty_imp.exec: Empty token queue!"
    | _ :: _ -> failwith "Pretty_imp.exec: Unclosed blocks!"
    | _ -> failwith "Pretty_imp.exec: Impossible: empty token_stack queue!"
  ;;

end;; (* struct *)

module Pretty = struct

  (*include Pretty_imp;;*)

  let margin = ref 60;;

  let print_stdout printer data =
    let st = Pretty_imp.empty () in
    printer st data;
    let tok = Pretty_imp.to_token st in
    let apps = Pretty_core.print (!margin) tok in
    App_list.iter Text_io.print apps;;

  let print_with_fmt printer fmt data =
    let st = Pretty_imp.empty () in
    printer st data;
    let tok = Pretty_imp.to_token st in
    let apps = Pretty_core.print (!margin) tok in
    App_list.iter (Text_io.output fmt) apps;;

  let print_to_string printer data =
    let st = Pretty_imp.empty () in
    printer st data;
    let tok = Pretty_imp.to_token st in
    let apps = Pretty_core.print (!margin) tok in
    App_list.concat apps;;

end;; (* struct *)

(* -------------------------------------------------------------------------
   format.ml compatibility layer
   ------------------------------------------------------------------------- *)

let set_margin n =
  if n < 1 then failwith "set_margin: must be positive";
  Pretty.margin := n
;;

type formatter = Pretty_imp.state;;

let pp_print_string = Pretty_imp.print_string;;
let pp_print_break = Pretty_imp.print_break;;
let pp_print_space fmt () = Pretty_imp.print_space fmt;;
let pp_print_newline fmt () = Pretty_imp.print_newline fmt;;

let pp_open_box = Pretty_imp.open_block;;
let pp_open_hbox fmt () = Pretty_imp.open_hblock fmt;;
let pp_open_vbox = Pretty_imp.open_vblock;;
let pp_open_hvbox = Pretty_imp.open_hvblock;;
let pp_close_box fmt () = Pretty_imp.close_block fmt;;

let print_to_string = Pretty.print_to_string;;

(* Functions that print to stdout: *)

let print_string = Pretty.print_stdout pp_print_string;;
let print_break l i =
  Pretty.print_stdout (fun s (l,i) -> pp_print_break s l i) (l, i);;
let print_space () = Pretty.print_stdout pp_print_space ();;
let print_newline () = Pretty.print_stdout pp_print_newline ();;
let print_endline s = print_string s; print_newline ();;

let open_box = Pretty.print_stdout pp_open_box;;
let open_hbox () = Pretty.print_stdout pp_open_hbox ();;
let open_vbox = Pretty.print_stdout pp_open_vbox;;
let open_hvbox = Pretty.print_stdout pp_open_hvbox;;
let close_box () = Pretty.print_stdout pp_close_box ();;

