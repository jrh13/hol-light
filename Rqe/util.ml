(* ---------------------------------------------------------------------- *)
(*  Strings                                                               *)
(* ---------------------------------------------------------------------- *)


let string_of_char c = String.make 1 c;;



(* ---------------------------------------------------------------------- *)
(*  Types                                                                 *)
(* ---------------------------------------------------------------------- *)


let gensort = sort (<);;
let suppress = ref ([]:string list);;
suppress := ["==>";"?";"!";"/\\";"\\/";",";"~";"APPEND";"CONS";"HD";"LAST";
  "NIL";"=";"real_lt";"real_gt";"real_le";"real_ge";"BIT0";"BIT1";"NUMERAL";
  "real_of_num";"_0";"_1";"real_div";"real_mul";"real_pow";"COND"];;

let rec get_type_list tm =
  match tm with
      Var(s,t) -> if mem s !suppress then [] else [(s,t)]
    | Const(s,t) -> if mem s !suppress then [] else [(s,t)]
    | Comb (t1,t2) -> get_type_list t1 @ get_type_list t2
    | Abs (t1,t2) -> get_type_list t1 @ get_type_list t2;;

let my_print_type (s,t) =
  print_string ("(\"" ^ s ^ "\", ");
  print_qtype t;
  print_string ")\n";;

let rec my_print_typel l =
  match l with
      [] -> ();
    | (h::t) -> my_print_type h; my_print_typel t;;

let set_types tm = (gensort o setify o get_type_list) tm;;

let print_term_types  = my_print_typel o set_types;;
let print_thm_types tm = print_term_types (concl tm);;
let goal_types() = (print_term_types o snd o top_goal)();;

let assum i = (rev_ith i o fst o top_goal)();;
let assum_types i = (print_term_types o rev_ith i o fst o top_goal)();;

let (get_type:string->thm->hol_type) =
  fun s thm -> assoc s (get_type_list (concl thm));;


(* ---------------------------------------------------------------------- *)
(* Proof Stack                                                            *)
(* ---------------------------------------------------------------------- *)

exception Empty_stack;;
let proof_stack = ref ([]:goalstack list);;
let push_proof t =
  proof_stack := [!current_goalstack] @ !proof_stack;
  g t;;

let pop_proof() =
  match !proof_stack with
      [] -> raise Empty_stack
    | h::t -> current_goalstack := h; proof_stack := t;
        p();;

(* ---------------------------------------------------------------------- *)
(*  Printing                                                              *)
(* ---------------------------------------------------------------------- *)

let print_thm_no_hyps th =
  let asl,tm = dest_thm th in
  (if not (asl = []) then
     print_string "..."
   else ();
   open_hbox();
   print_string "|- ";
   print_term tm;
   close_box());;


let print_trace_thm hyps msg th =
  let asl,tm = dest_thm th in
   open_hbox();
   print_string "------------------------\n ";
   print_string (msg ^ "\n");
   if hyps then print_thm th else print_thm_no_hyps th;
   print_string "\n========================\n ";
   close_box();;

(*
#install_printer print_thm_no_hyps;;
#install_printer print_thm;;
*)


