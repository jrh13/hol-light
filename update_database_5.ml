(* ========================================================================= *)
(* Create search database from OCaml / modify search database dynamically.   *)
(*                                                                           *)
(* This file assigns to "theorems", which is a list of name-theorem pairs.   *)
(* The core system already has such a database set up. Use this file if you  *)
(* want to update the database beyond the core, so you can search it.        *)
(*                                                                           *)
(* The trickery to get at the OCaml environment is due to Roland Zumkeller   *)
(* and Michael Farber. It works by copying some internal data structures and *)
(* casting into the copy using Obj.magic.                                    *)
(* ========================================================================= *)

Format.print_string
 ("**** WARNING: Dynamic updating does not yet work in OCaml version 5.xx\n" ^
  "**** FOR NOW update_database() HAS NO EFFECT ***\n");;

let update_database() =
  Format.print_string("*** NOT YET SUPPORTED IN Ocaml >= 5\n");;

let make_database_assignment (s:string) =
  Format.print_string("*** NOT YET SUPPORTED IN Ocaml >= 5\n");;
