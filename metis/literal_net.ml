(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* ========================================================================= *)

module Literal_net = struct

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = Atom_net.parameters;;

type 'a literalNet = Literal_net of {
  positive : 'a Atom_net.atomNet;
  negative : 'a Atom_net.atomNet
};;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet parm =
  Literal_net {
    positive = Atom_net.newNet parm;
    negative = Atom_net.newNet parm
};;

let pos (Literal_net {positive}) = Atom_net.size positive;;

let neg (Literal_net {negative}) = Atom_net.size negative;;

let size net = pos net + neg net;;

let insert (Literal_net {positive; negative}) = function
  | ((true,atm),a) ->
      Literal_net {positive = Atom_net.insert positive (atm,a);
                   negative = negative}
  | ((false,atm),a) ->
      Literal_net {positive = positive;
                   negative = Atom_net.insert negative (atm,a)};;

let fromList parm l =
  List.foldl (fun lit_a n -> insert n lit_a) (newNet parm) l;;

let filter pred (Literal_net {positive; negative}) =
  Literal_net {
    positive = Atom_net.filter pred positive;
    negative = Atom_net.filter pred negative
  };;

let toString net = "Literal_net[" ^ Int.toString (size net) ^ "]";;

(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

let matchNet (Literal_net {positive; negative}) = function
  | (true,atm) -> Atom_net.matchNet positive atm
  | (false,atm) -> Atom_net.matchNet negative atm;;

let matched (Literal_net {positive; negative}) = function
  | (true,atm) -> Atom_net.matched positive atm
  | (false,atm) -> Atom_net.matched negative atm;;

let unify (Literal_net {positive; negative}) = function
  | (true,atm) -> Atom_net.unify positive atm
  | (false,atm) -> Atom_net.unify negative atm;;

end (* struct Literal_net *)
;;
