module Mmap = struct
type ('k, 'v) map = Mmap of ('k, 'v) Map.map;;
let newMap cmp () = Mmap (Map.empty cmp);;
let null (Mmap m) = Map.null m;;
let singleton cmp (k, x) = Mmap (Map.insert (Map.empty cmp) k x);;
let size (Mmap m) = Map.size m;;
let get (Mmap m) k =
  match Map.lookup m k with
  | None -> raise (Error "Mmap.get: element not found")
  | Some v -> v;;
let peek (Mmap m) k = Map.lookup m k;;
let insert (Mmap m) (k, v) = Mmap (Map.insert m k v);;
let toList (Mmap m) = Map.toAscList m;;
let fromList cmp l = Mmap (Map.fromList cmp l);;
let foldr f b (Mmap m) =
  Map.foldrWithKey (fun k v s -> f (k, v, s)) b m;;
let foldl = foldr;;
let filter f (Mmap m) = Mmap (Map.filterWithKey (fun k v -> f (k, v)) m);;
let inDomain k (Mmap m) = Option.isSome (Map.lookup m k);;
let union f (Mmap m1) (Mmap m2) =
  let m1 = Map.map (fun x -> Some x) m1
  and m2 = Map.map (fun x -> Some x) m2 in
  let f' k = function
    | Some x, Some y -> f ((k, x), (k, y))
    | Some x, _ -> Some x
    | _, Some y -> Some y
    | _ -> None in
  let m = Map.unionWithKey (fun k x y -> f' k (x, y)) m1 m2 in
  let m = Map.filter Option.isSome m in
  Mmap (Map.map Option.valOf m);;
let delete (Mmap m) k = Mmap (Map.delete m k);;
let mapPartial cmp f (Mmap m) =
  Mmap (Map.foldrWithKey (fun k x acc ->
    match f (k, x) with
    | Some y -> Map.insert acc k y
    | None -> acc) (Map.empty cmp) m);;
let transform f (Mmap m) = Mmap (Map.map f m);;
let exists f (Mmap m) = Map.exists f m;;
end (* struct Mmap *)
;;

module Intmap = struct
let cmp = Int.compare
let newMap () = Mmap.newMap cmp ();;
let singleton kv = Mmap.singleton cmp kv;;
let fromList xs = Mmap.fromList cmp xs;;
let mapPartial f m = Mmap.mapPartial cmp f m;;
let null = Mmap.null and size = Mmap.size and get = Mmap.get
and peek = Mmap.peek and insert = Mmap.insert and toList = Mmap.toList
and foldl = Mmap.foldl and foldr = Mmap.foldr and filter = Mmap.filter
and inDomain = Mmap.inDomain and union = Mmap.union and delete = Mmap.delete
and transform = Mmap.transform and exists = Mmap.exists;;
end (* struct IntMap *)
;;

module Stringmap = struct
let cmp = String.compare
let newMap () = Mmap.newMap cmp ();;
let singleton kv = Mmap.singleton cmp kv;;
let fromList xs = Mmap.fromList cmp xs;;
let mapPartial f m = Mmap.mapPartial cmp f m;;
let null = Mmap.null and size = Mmap.size and get = Mmap.get
and peek = Mmap.peek and insert = Mmap.insert and toList = Mmap.toList
and foldl = Mmap.foldl and foldr = Mmap.foldr and filter = Mmap.filter
and inDomain = Mmap.inDomain and union = Mmap.union and delete = Mmap.delete
and transform = Mmap.transform and exists = Mmap.exists;;
end (* struct Stringmap *)
;;
