(* ========================================================================= *)
(*                              Isabelle Light                               *)
(*   Isabelle/Procedural style additions and other user-friendly shortcuts.  *)
(*                                                                           *)
(*                   Petros Papapanagiotou, Jacques Fleuriot                 *)
(*              Center of Intelligent Systems and their Applications         *)
(*                          University of Edinburgh                          *)
(*                                 2009-2012                                 *)
(* ========================================================================= *)
(* FILE         : make.ml                                                    *)
(* DESCRIPTION  : Makefile. Simply calls the loader but it was written to    *)
(*                match the rest of HOL Light's packages and for future use. *)
(* LAST MODIFIED: October 2010                                               *)
(* ========================================================================= *)

loads "IsabelleLight/isalight.ml";;

(* Some examples: *)

prove( `p/\q==>q`, rule impI THEN erule conjE THEN assumption);;
prove (`(!x. P x) ==> P (y+1)`, rule impI THEN erule_tac [`a`,`y+1`] allE THEN assumption);;
prove (`p\/q==>q\/p`, rule impI THEN erule disjE THENL [ rule disjI2 ; rule disjI1 ] THEN assumption);;
prove (`p/\q ==> p\/q`, rule impI THEN rule disjI1 THEN drule conjunct1 THEN assumption);;
prove (`p/\q ==> p\/q`, DISCH_TAC THEN DISJ1_TAC THEN FIRST_ASSUM(CONJUNCTS_THEN ACCEPT_TAC));;
prove (`P x /\ x =0 ==> P 0`, rule impI THEN erule conjE THEN simp[]);;
