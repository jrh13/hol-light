(* ========================================================================= *)
(* NAME/ARITY PAIRS                                                          *)
(* ========================================================================= *)

module Name_arity = struct

open Useful;;
open Order

(* ------------------------------------------------------------------------- *)
(* A type of name/arity pairs.                                               *)
(* ------------------------------------------------------------------------- *)

type nameArity = Name.name * int;;

let name ((n,_) : nameArity) = n;;

let arity ((_,i) : nameArity) = i;;

(* ------------------------------------------------------------------------- *)
(* Testing for different arities.                                            *)
(* ------------------------------------------------------------------------- *)

let nary i n_i = arity n_i = i;;

let nullary = nary 0
and unary = nary 1
and binary = nary 2
and ternary = nary 3;;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

let compare ((n1,i1),(n2,i2)) =
    match Name.compare (n1,n2) with
      Less -> Less
    | Equal -> Int.compare (i1,i2)
    | Greater -> Greater;;

let equal (n1,i1) (n2,i2) = i1 = i2 && Name.equal n1 n2;;


module Ordered =
struct type t = nameArity let compare = fromCompare compare end

module Map = struct
  include Mmap.Make (Ordered)

  let compose m1 m2 =
      let pk ((_,a),n) = peek m2 (n,a)
    in
      mapPartial pk m1
    ;;
end

module Set = struct
  include Mset.Make (Ordered)

  let allNullary = all nullary;
end

end

