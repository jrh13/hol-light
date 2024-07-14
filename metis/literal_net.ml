(* ========================================================================= *)
(* MATCHING AND UNIFICATION FOR SETS OF FIRST ORDER LOGIC LITERALS           *)
(* ========================================================================= *)

module Literal_net = struct

open Useful;;

(* ------------------------------------------------------------------------- *)
(* A type of literal sets that can be efficiently matched and unified.       *)
(* ------------------------------------------------------------------------- *)

type parameters = Atom_net.parameters;;

type 'a literalNet =
    {positive : 'a Atom_net.atomNet;
     negative : 'a Atom_net.atomNet};;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let newNet parm = {positive = Atom_net.newNet parm; negative = Atom_net.newNet parm};;

  let pos ({positive=positive} : 'a literalNet) = Atom_net.size positive;;

  let neg ({negative=negative} : 'a literalNet) = Atom_net.size negative;;

  let size net = pos net + neg net;;

  (*let profile net = {positiveN = pos net; negativeN = neg net};;*)


let insert {positive=positive;negative=negative} = function
    ((true,atm),a) ->
    {positive = Atom_net.insert positive (atm,a); negative = negative}
  | ((false,atm),a) ->
    {positive = positive; negative = Atom_net.insert negative (atm,a)};;

let fromList parm l = Mlist.foldl (fun (lit_a,n) -> insert n lit_a) (newNet parm) l;;

let filter pred {positive=positive;negative=negative} =
    {positive = Atom_net.filter pred positive;
     negative = Atom_net.filter pred negative};;

let toString net = "Literal_net[" ^ Int.toString (size net) ^ "]";;


(* ------------------------------------------------------------------------- *)
(* Matching and unification queries.                                         *)
(*                                                                           *)
(* These function return OVER-APPROXIMATIONS!                                *)
(* Filter afterwards to get the precise set of satisfying values.            *)
(* ------------------------------------------------------------------------- *)

let matchNet ({positive=positive;negative=negative} : 'a literalNet) = function
    (true,atm) ->
    Atom_net.matchNet positive atm
  | (false,atm) -> Atom_net.matchNet negative atm;;

let matched ({positive=positive;negative=negative} : 'a literalNet) = function
    (true,atm) ->
    Atom_net.matched positive atm
  | (false,atm) -> Atom_net.matched negative atm;;

let unify ({positive=positive;negative=negative} : 'a literalNet) = function
    (true,atm) ->
    Atom_net.unify positive atm
  | (false,atm) -> Atom_net.unify negative atm;;

end



