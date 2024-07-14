module Mmap = struct

exception Error = Useful.Error;;

module Make (Ord : Ordered) =
struct
  module Ma = Map.Make (Ord)

  type +'a map = 'a Ma.t

  let newMap () = Ma.empty;;
  let null = Ma.is_empty;;
  let singleton (k, x) = Ma.singleton k x;;
  let size = Ma.cardinal;;
  let get m k = try Ma.find k m with Not_found -> raise (Error "Mmap.get: element not found");;
  let peek m k = try Some (Ma.find k m) with Not_found -> None;;
  let insert m (k, v) = Ma.add k v m;;
  let toList = Ma.bindings;;
  let fromList l = List.fold_right (fun (v,tm) -> Ma.add v tm) l Ma.empty;;
  let foldl f b m = List.fold_left (fun s (v, tm) -> f (v, tm, s)) b (Ma.bindings m);;
  let foldr = foldl;;
  let filter f = Ma.filter (fun x y -> f (x, y));;
  let inDomain = Ma.mem;;
  let union f m1 m2 =
    let f' k = function
        (Some x, Some y) -> f ((k, x), (k, y))
      | (Some x, None) -> Some x
      | (None, Some y) -> Some y
      | (None, None) -> None
    in Ma.merge (fun k x y -> f' k (x, y)) m1 m2
  let delete m k = Ma.remove k m
  let mapPartial f m = Ma.fold (fun k x acc -> match f (k, x) with Some y -> Ma.add k y acc | None -> acc) m Ma.empty;;
  let transform = Ma.map;;
  let exists f = Ma.exists (fun k m -> f (k,m));;
end
end

module Intmap = struct

open Order

module Ordered = struct type t = int let compare = compare end

include Mmap.Make (Ordered);;

end

module Stringmap = struct

open Order

module Ordered = struct type t = string let compare = compare end

include Mmap.Make (Ordered);;

end
