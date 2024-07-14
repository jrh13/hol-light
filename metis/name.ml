(* ========================================================================= *)
(* NAMES                                                                     *)
(* ========================================================================= *)

module Name = struct

open Useful;;

(* ------------------------------------------------------------------------- *)
(* A type of names.                                                          *)
(* ------------------------------------------------------------------------- *)

type name = string;;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

let compare = Order.toCompare (compare : name -> name -> int);;

let equal n1 n2 = n1 = n2;;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

let prefix  = "_";;
let numName i = mkPrefix prefix (Int.toString i);;
let newName () = numName (newInt ());;
let newNames n = List.map numName (newInts n);;

let variantPrime avoid =
    let rec variant n = if avoid n then variant (n ^ "'") else n
    in variant;;

let variantNum avoid n =
  let isDigitOrPrime c = c = '\'' || isDigit c
  in if not (avoid n) then n
      else
        let n = stripSuffix isDigitOrPrime n in
        let rec variant i =
          let n_i = n ^ Int.toString i
          in if avoid n_i then variant (i + 1) else n_i
        in variant 0
;;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

let toString s : string = s;;

let fromString s : name = s;;

module Ordered =
struct type t = name let compare = Order.fromCompare compare end

module Map = Mmap.Make (Ordered);;
module Set = Mset.Make (Ordered);;

end
