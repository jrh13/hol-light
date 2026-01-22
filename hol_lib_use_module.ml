(* ========================================================================= *)
(*                               HOL LIGHT                                   *)
(*                                                                           *)
(*              Modern OCaml version of the HOL theorem prover               *)
(*                                                                           *)
(*                            John Harrison                                  *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2024                       *)
(*              (c) Copyright, Juneyoung Lee 2024                            *)
(* ========================================================================= *)

Topdirs.dir_load Format.std_formatter
  (Filename.concat (!hol_dir) "hol_lib.cmo");;
include Hol_lib;;