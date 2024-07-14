module Mset = struct

module type Ordered =
sig
  type t
  val compare : t -> t -> int
end

module Make (Ord : Ordered) =
struct
  module Se = Set.Make (Ord)

  type set = Se.t;;
  let compare = Order.toCompare Se.compare;;

  let add s x = Se.add x s;;
  let foldr f a s = Se.fold (fun x acc -> f (x,acc)) s a;;
  let foldl = foldr;;
  let member = Se.mem;;
  let empty = Se.empty;;
  let union = Se.union;;
  let difference = Se.diff;;
  let toList = Se.elements;;
  let singleton = Se.singleton;;
  let null = Se.is_empty;;
  let size = Se.cardinal;;
  let pick = Se.choose;;
  let equal = Se.equal;;
  let exists = Se.exists;;
  let fromList l = List.fold_right Se.add l Se.empty;;
  let delete s x = Se.remove x s;;
  let subset = Se.subset;;
  let intersect = Se.inter;;
  let intersectList = function
      [] -> Se.empty
    | (s::ss) -> List.fold_right Se.inter ss s
  let findl p s =
    let go x = function
        (Some _) as s -> s
      | None -> if p x then Some x else None
    in Se.fold go s None;;
  let firstl f s =
    let go x = function
        (Some _) as s -> s
      | None -> f x
     in Se.fold go s None;;
  let transform f s = Se.fold (fun x acc -> f x :: acc) s []
  let all = Se.for_all;;
  let count p s = Se.fold (fun x c -> if p x then c+1 else c) s 0
end

end


module Intset = struct

open Order

module Ordered = struct type t = int let compare = compare end

include Mset.Make (Ordered);;

end
