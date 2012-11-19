(* ========================================================================= *)
(*                              Isabelle Light                               *)
(*   Isabelle/Procedural style additions and other user-friendly shortcuts.  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2012                                 *)
(* ========================================================================= *)
(* FILE         : isahol.ml                                                  *)
(* DESCRIPTION  : Main loader.                                               *)
(* LAST MODIFIED: December 2010                                              *)
(* ========================================================================= *)

let paths = [".";"$/IsabelleLight"]
in map (fun st -> load_on_path paths st)
        ["support.ml";
         "new_tactics.ml";
         "meta_rules.ml"];;
