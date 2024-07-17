module Metis_debug = struct

(* Taken from: https://sourceforge.net/p/hol/mailman/message/35201767/ *)
let print_varandtype fmt tm =
  let hop,args = strip_comb tm in
  let s = name_of hop
  and ty = type_of hop in
  if is_var hop && args = [] then
    begin
      pp_print_string fmt "(";
      pp_print_string fmt s;
      pp_print_string fmt ":";
      pp_print_type fmt ty;
      pp_print_string fmt ")"
    end
  else fail()
;;

let show_types,hide_types =
  (fun () -> install_user_printer ("Show Types", print_varandtype)),
   fun () ->
     try delete_user_printer "Show Types"
     with Failure _ ->
       failwith ("hide_types: Types are already hidden.");;

end (* struct Metis_debug *)
