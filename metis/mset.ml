module Mset = struct
type 'k set = Mset of 'k Set.set;;
let add (Mset s) x = Mset (Set.insert x s);;
let foldr f a (Mset s) = Set.fold (curry f) a s;;
let foldl = foldr;;
let member x (Mset s) = Set.member x s;;
let empty cmp = Mset (Set.empty cmp);;
let union (Mset s1) (Mset s2) = Mset (Set.union s1 s2);;
let difference (Mset s1) (Mset s2) =
  Mset (Set.fold (fun k acc ->
    if Set.member k s1 then Set.delete k acc else acc) s1 s2);;
let toList (Mset s) = Set.toList s;;
let singleton cmp k = Mset (Set.singleton cmp k);;
let null (Mset s) = Set.null s;;
let size (Mset s) = Set.size s;;
let pick (Mset s) =
  (* Hack: *)
  let x = ref [] in
  try Set.map (fun k -> x := [k]; failwith "") s; List.hd (!x)
  with Failure _ -> List.hd (!x)
;;
let equal (Mset s1) (Mset s2) =
  Set.isSubset s1 s2 &&
  Set.isSubset s2 s1;;
let exists f (Mset s) = Set.exists f s;;
let fromList cmp l = Mset (Set.fromList cmp l);;
let delete (Mset s) k = Mset (Set.delete k s);;
let subset (Mset s1) (Mset s2) = Set.isSubset s1 s2;;
let intersect cmp (Mset s1) (Mset s2) =
  Mset (Set.fold (fun k acc ->
    if Set.member k s2 then Set.insert k acc else acc) (Set.empty cmp) s1);;
let intersectList cmp = function
  | [] -> Mset (Set.empty cmp)
  | s::ss -> List.foldr (intersect cmp) s ss;;
let findl p (Mset s) =
  Set.fold (fun k acc ->
    match acc with
    | Some _ -> acc
    | None -> if p k then Some k else None) None s;;
let firstl f (Mset s) =
  Set.fold (fun k acc ->
    match acc with
    | Some _ -> acc
    | None -> f k) None s;;
let transform f (Mset s) =
  Set.fold (fun x acc -> f x :: acc) [] s;;
let all p (Mset s) = Set.all p s;;
let count p (Mset s) =
  Set.fold (fun x c -> if p x then c+1 else c) 0 s;;
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
