(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC ATOMS              *)
(* ========================================================================= *)

module Atom_net = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let atomToTerm atom = Term.Fn atom;;

let termToAtom = function
  | (Term.Var_ _) -> raise (Bug "Atom_net.termToAtom")
  | (Term.Fn atom) -> atom;;

(* ------------------------------------------------------------------------- *)
(* A type of atom sets that can be efficiently matched and unified.          *)
(* ------------------------------------------------------------------------- *)

type parameters = Term_net.parameters;;

type 'a atomNet = 'a Term_net.termNet;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet = Term_net.newNet;;

let size = Term_net.size;;

let insert net (atm,a) = Term_net.insert net (atomToTerm atm, a);;

let fromList parm l =
  List.foldl (fun atm_a n -> insert n atm_a) (newNet parm) l;;

let filter = Term_net.filter;;

let toString net = "Atom_net[" ^ Int.toString (size net) ^ "]";;


(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

let matchNet net atm = Term_net.matchNet net (atomToTerm atm);;

let matched net atm = Term_net.matched net (atomToTerm atm);;

let unify net atm = Term_net.unify net (atomToTerm atm);;

end (* struct Atom_net *)
;;
