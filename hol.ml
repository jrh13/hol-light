(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

let hol_version = "3.1.0";;

(* ------------------------------------------------------------------------- *)
(* Should eventually change to "ref(Filename.temp_dir_name)".                *)
(* However that's not available in 3.08, which is still the default          *)
(* in Cygwin, and I don't want to force people to upgrade Ocaml.             *)
(* ------------------------------------------------------------------------- *)

let temp_path = ref "/tmp";;

(* ------------------------------------------------------------------------- *)
(* Load the load/need functions.                                             *)
(* ------------------------------------------------------------------------- *)

loads "hol_loader.ml"

(* ------------------------------------------------------------------------- *)
(* Load the core files.                                                      *)
(* ------------------------------------------------------------------------- *)

(*
let use_module =
  try Sys.getenv "HOLLIGHT_USE_MODULE" = "1" with Not_found -> false;;
if use_module
then loads "hol_lib_use_module.ml"
else loads "hol_lib.ml";;
*)
loads "hol_lib.ml";;

(* ------------------------------------------------------------------------- *)
(* Install printers.                                                         *)
(* ------------------------------------------------------------------------- *)

(*
#install_printer pp_print_num;;

#install_printer pp_print_fpf;;

let set_color_printer (use_color:bool) =
  let printers =
    if use_color
    then ["pp_print_colored_qterm"; "pp_print_colored_qtype";
          "pp_print_colored_thm"; "pp_print_colored_goal";
          "pp_print_colored_goalstack"]
    else ["pp_print_qterm"; "pp_print_qtype"; "pp_print_thm"; "pp_print_goal";
          "pp_print_goalstack"] in
  let _ = map (fun name ->
      Topdirs.dir_install_printer Format.std_formatter (Lident name))
    printers in
  ();;

set_color_printer true;;
*)

(* ------------------------------------------------------------------------- *)
(* In-logic computation function.                                            *)
(* ------------------------------------------------------------------------- *)

loads "candle_compute.ml";; (* Definitions of cval primitives                *)

(* ------------------------------------------------------------------------- *)
(* The help system.                                                          *)
(* ------------------------------------------------------------------------- *)


(*
loads "help.ml";;       (* Online help using the entries in Help directory   *)
loads "database.ml";;   (* List of name-theorem pairs for search system      *)
*)
