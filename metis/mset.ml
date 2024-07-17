module Mset = struct
type 'k set = Mset of ('k, unit) Map.map;;
let the_unit = ();;
let add (Mset s) x = Mset (Map.insert s x the_unit);;
let foldr f a (Mset s) =
  Map.foldrWithKey (fun k _ acc -> f (k, acc)) a s;;
let foldl = foldr;;
let member x (Mset s) = Option.isSome (Map.lookup s x);;
let empty cmp = Mset (Map.empty cmp);;
let union (Mset s1) (Mset s2) = Mset (Map.union s1 s2);;
let difference (Mset s1) (Mset s2) =
  Mset (Map.foldrWithKey (fun k _ acc ->
    if Option.isSome (Map.lookup s1 k) then Map.delete acc k else acc) s1 s2);;
let toList (Mset s) = List.map fst (Map.toAscList s);;
let singleton cmp k = Mset (Map.insert (Map.empty cmp) k the_unit);;
let null (Mset s) = Map.null s;;
let size (Mset s) = Map.size s;;
let pick (Mset s) =
  (* Hack: *)
  let x = ref [] in
  try Map.mapWithKey (fun k () -> x := [k]; failwith "") s; List.hd (!x)
  with Failure _ -> List.hd (!x)
;;
let equal (Mset s1) (Mset s2) = s1 = s2;;
let exists f (Mset s) = Map.exists (fun k _ -> f k) s;;
let fromList cmp l =
  Mset (List.foldr (fun k m -> Map.insert m k the_unit) (Map.empty cmp) l);;
let delete (Mset s) k = Mset (Map.delete s k);;
let subset (Mset s1) (Mset s2) = Map.isSubmap s1 s2;;
let intersect cmp (Mset s1) (Mset s2) =
  Mset (Map.foldrWithKey (fun k _ acc ->
    if Option.isSome (Map.lookup s2 k) then Map.insert acc k the_unit
    else acc) (Map.empty cmp) s1);;
let intersectList cmp = function
  | [] -> Mset (Map.empty cmp)
  | s::ss -> List.foldr (intersect cmp) s ss;;
let findl p (Mset s) =
  Map.foldrWithKey (fun k () acc ->
    match acc with
    | Some _ -> acc
    | None -> if p k then Some k else None) None s;;
let firstl f (Mset s) =
  Map.foldrWithKey (fun k () acc ->
    match acc with
    | Some _ -> acc
    | None -> f k) None s;;
(* TODO Urk: *)
let transform f (Mset s) =
  Map.foldrWithKey (fun x _ acc -> f x :: acc) [] s;;
let all p (Mset s) = Map.all (fun k () -> p k) s;;
let count p (Mset s) =
  Map.foldrWithKey (fun x () c -> if p x then c+1 else c) 0 s;;
end (* struct Mset *)
;;

module Intset = struct
let cmp = Int.compare;;
let empty : int Mset.set = Mset.empty cmp;;
let singleton k = Mset.singleton cmp k;;
let intersect m1 m2 = Mset.intersect cmp;;
let intersectList = Mset.intersectList cmp;;
let fromList = Mset.fromList cmp;;
let add = Mset.add and foldr = Mset.foldr and foldl = Mset.foldl
and member = Mset.member and union = Mset.union and difference = Mset.difference
and toList = Mset.toList and null = Mset.null and size = Mset.size
and pick = Mset.pick and equal = Mset.equal and exists = Mset.exists
and delete = Mset.delete and subset = Mset.subset and findl = Mset.findl
and firstl = Mset.firstl and transform = Mset.transform and all = Mset.all
and count = Mset.count;;
end
;;
