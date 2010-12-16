(* ========================================================================= *)
(* Some miscellaneous OCaml system hacking before we get started.            *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

Gc.set { (Gc.get()) with Gc.stack_limit = 16777216 };;

(* ------------------------------------------------------------------------- *)
(* Make sure user interrupts generate an exception, not kill the process.    *)
(* ------------------------------------------------------------------------- *)

Sys.catch_break true;;

(* ------------------------------------------------------------------------- *)
(* Set up a quotation expander for the `...` quotes.                         *)
(* ------------------------------------------------------------------------- *)

let quotexpander s =
  if String.sub s 0 1 = ":" then
    "parse_type \""^
    (String.escaped (String.sub s 1 (String.length s - 1)))^"\""
  else "parse_term \""^(String.escaped s)^"\"";;

Quotation.add "tot" (Quotation.ExStr (fun x -> quotexpander));;

(* ------------------------------------------------------------------------- *)
(* Modify the lexical analysis of uppercase identifiers.                     *)
(* ------------------------------------------------------------------------- *)

set_jrh_lexer;;

(* ------------------------------------------------------------------------- *)
(* Load in the bignum library and set up printing in the toplevel.           *)
(* ------------------------------------------------------------------------- *)

#load "nums.cma";;

include Num;;

let print_num n =
  Format.open_hbox();
  Format.print_string(string_of_num n);
  Format.close_box();;

#install_printer print_num;;
