(* ========================================================================= *)
(* Some miscellaneous OCaml system hacking before we get started.            *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2014                       *)
(* ========================================================================= *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };;

(* ------------------------------------------------------------------------- *)
(* Make sure user interrupts generate an exception, not kill the process.    *)
(* ------------------------------------------------------------------------- *)

Sys.catch_break true;;

(* ------------------------------------------------------------------------- *)
(* Set up a printer for num.                                                 *)
(* ------------------------------------------------------------------------- *)

let pp_print_num fmt n =
  Format.pp_open_hbox fmt ();
  Format.pp_print_string fmt (string_of_num n);
  Format.pp_close_box fmt ();;

let print_num x = pp_print_num (Hol_domains.std_formatter ()) x;;
