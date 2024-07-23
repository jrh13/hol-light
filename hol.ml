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

let hol_version = "2.20++";;

let hol_dir = ref "hol-light/";;

(* ------------------------------------------------------------------------- *)
(* Should eventually change to "ref(Filename.temp_dir_name)".                *)
(* However that's not available in 3.08, which is still the default          *)
(* in Cygwin, and I don't want to force people to upgrade Ocaml.             *)
(* ------------------------------------------------------------------------- *)

let temp_path = ref "/tmp";;

(* ------------------------------------------------------------------------- *)
(* Various tweaks to OCaml and general library functions.                    *)
(* ------------------------------------------------------------------------- *)

loads "system.ml";;      (* Set up proper parsing                            *)
loads "candle_nums.ml";; (* Load bignums                                     *)
loads "lib.ml";;         (* Various useful general library functions         *)

(* ------------------------------------------------------------------------- *)
(* Candle things.                                                            *)
(* ------------------------------------------------------------------------- *)

loads "candle_kernel.ml";;               (* Brings Candle kernel into scope. *)
loads "candle_pretty.ml";;               (* Pretty printer code.             *)

(* ------------------------------------------------------------------------- *)
(* Some extra support stuff needed outside the core.                         *)
(* ------------------------------------------------------------------------- *)

loads "basics.ml";;     (* Additional syntax operations and other utilities  *)
loads "nets.ml";;       (* Term nets for fast matchability-based lookup      *)

(* ------------------------------------------------------------------------- *)
(* The interface.                                                            *)
(* ------------------------------------------------------------------------- *)

loads "printer.ml";;    (* Crude prettyprinter                               *)
loads "preterm.ml";;    (* Preterms and their interconversion with terms     *)
loads "parser.ml";;     (* Lexer and parser                                  *)

(* ------------------------------------------------------------------------- *)
(* Higher level deductive system.                                            *)
(* ------------------------------------------------------------------------- *)

loads "equal.ml";;      (* Basic equality reasoning and conversionals        *)
loads "bool.ml";;       (* Boolean theory and basic derived rules            *)
loads "drule.ml";;      (* Additional derived rules                          *)
loads "tactics.ml";;    (* Tactics, tacticals and goal stack                 *)
loads "itab.ml";;       (* Toy prover for intuitionistic logic               *)
loads "simp.ml";;       (* Basic rewriting and simplification tools          *)

loads "theorems.ml";;   (* Additional theorems (mainly for quantifiers) etc. *)
loads "ind_defs.ml";;   (* Derived rules for inductive definitions           *)
loads "class.ml";;      (* Classical reasoning: Choice and Extensionality    *)
loads "trivia.ml";;     (* Some very basic theories, e.g. type ":1"          *)
loads "canon.ml";;      (* Tools for putting terms in canonical forms        *)
loads "meson.ml";;      (* First order automation: MESON (model elimination) *)
loads "metis.ml";;      (* More advanced first-order automation: Metis       *)

(*
(*
loads "firstorder.ml";; (* More utilities for first-order shadow terms       *)
loads "thecops.ml";;    (* Connection-based automation: leanCoP and nanoCoP  *)
*)

loads "quot.ml";;       (* Derived rules for defining quotient types         *)
loads "impconv.ml";;    (* More powerful implicational rewriting etc.        *)

(* ------------------------------------------------------------------------- *)
(* Mathematical theories and additional proof tools.                         *)
(* ------------------------------------------------------------------------- *)

loads "pair.ml";;       (* Theory of pairs                                   *)
(*
loads "compute.ml";;    (* General call-by-value reduction tool for terms    *)
*)

loads "nums.ml";;       (* Axiom of Infinity, definition of natural numbers  *)
loads "recursion.ml";;  (* Tools for primitive recursion on inductive types  *)
loads "arith.ml";;      (* Natural number arithmetic                         *)
loads "wf.ml";;         (* Theory of wellfounded relations                   *)
loads "calc_num.ml";;   (* Calculation with natural numbers                  *)
loads "normalizer.ml";; (* Polynomial normalizer for rings and semirings     *)
loads "grobner.ml";;    (* Groebner basis procedure for most semirings       *)
loads "ind_types.ml";;  (* Tools for defining inductive types                *)
loads "lists.ml";;      (* Theory of lists                                   *)
loads "realax.ml";;     (* Definition of real numbers                        *)
loads "calc_int.ml";;   (* Calculation with integer-valued reals             *)
loads "realarith.ml";;  (* Universal linear real decision procedure          *)
loads "real.ml";;       (* Derived properties of reals                       *)

loads "calc_rat.ml";;   (* Calculation with rational-valued reals            *)
loads "int.ml";;        (* Definition of integers                            *)
loads "sets.ml";;       (* Basic set theory                                  *)
loads "iterate.ml";;    (* Iterated operations                               *)
loads "cart.ml";;       (* Finite Cartesian products                         *)
loads "define.ml";;     (* Support for general recursive definitions         *)

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
*)
