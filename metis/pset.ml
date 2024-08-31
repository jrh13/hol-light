(* ========================================================================= *)
(* FINITE SETS IMPLEMENTED WITH RANDOMLY BALANCED TREES                      *)
(* ========================================================================= *)

module Pset = struct

(* ------------------------------------------------------------------------- *)
(* A type of finite sets.                                                    *)
(* ------------------------------------------------------------------------- *)

type ('elt,'a) map = ('elt,'a) Pmap.map;;

type 'elt set = Set of ('elt,unit) map;;

(* ------------------------------------------------------------------------- *)
(* Converting to and from maps.                                              *)
(* ------------------------------------------------------------------------- *)

let dest (Set m) = m;;

let mapPartial f =
  let mf elt () = f elt in
  fun (Set m) -> Pmap.mapPartial mf m
;;

let map f =
  let mf elt () = f elt in
  fun (Set m) -> Pmap.map mf m
;;

let domain m = Set (Pmap.transform (fun _ _ -> ()) m);;

(* ------------------------------------------------------------------------- *)
(* Constructors.                                                             *)
(* ------------------------------------------------------------------------- *)

let empty cmp = Set (Pmap.newMap cmp);;

let singleton cmp elt = Set (Pmap.singleton cmp (elt,()));;

(* ------------------------------------------------------------------------- *)
(* Set size.                                                                 *)
(* ------------------------------------------------------------------------- *)

let null (Set m) = Pmap.null m;;

let size (Set m) = Pmap.size m;;

(* ------------------------------------------------------------------------- *)
(* Querying.                                                                 *)
(* ------------------------------------------------------------------------- *)

let peek (Set m) elt =
  match Pmap.peekKey m elt with
  | Some (elt,()) -> Some elt
  | None -> None;;

let member elt (Set m) = Pmap.inDomain elt m;;

let pick (Set m) =
  let (elt,_) = Pmap.pick m in
  elt
;;

let nth (Set m) n =
  let (elt,_) = Pmap.nth m n in
  elt
;;

let random (Set m) =
  let (elt,_) = Pmap.random m in
  elt
;;

(* ------------------------------------------------------------------------- *)
(* Adding.                                                                   *)
(* ------------------------------------------------------------------------- *)

let add (Set m) elt =
  let m = Pmap.insert m (elt,()) in
  Set m
;;

let uncurriedAdd elt set = add set elt;;
let addList set = List.foldl uncurriedAdd set;;

(* ------------------------------------------------------------------------- *)
(* Removing.                                                                 *)
(* ------------------------------------------------------------------------- *)

let delete (Set m) elt =
  let m = Pmap.delete m elt in
  Set m
;;

let remove (Set m) elt =
  let m = Pmap.remove m elt in
  Set m
;;

let deletePick (Set m) =
  let ((elt,()),m) = Pmap.deletePick m in
  (elt, Set m)
;;

let deleteNth (Set m) n =
  let ((elt,()),m) = Pmap.deleteNth m n in
  (elt, Set m)
;;

let deleteRandom (Set m) =
  let ((elt,()),m) = Pmap.deleteRandom m in
  (elt, Set m)
;;

(* ------------------------------------------------------------------------- *)
(* Joining.                                                                  *)
(* ------------------------------------------------------------------------- *)

let union (Set m1) (Set m2) = Set (Pmap.unionDomain m1 m2);;

let unionList sets =
  let ms = List.map dest sets in
  Set (Pmap.unionListDomain ms)
;;

let intersect (Set m1) (Set m2) = Set (Pmap.intersectDomain m1 m2);;

let intersectList sets =
  let ms = List.map dest sets in
  Set (Pmap.intersectListDomain ms)
;;

let difference (Set m1) (Set m2) =
  Set (Pmap.differenceDomain m1 m2);;

let symmetricDifference (Set m1) (Set m2) =
  Set (Pmap.symmetricDifferenceDomain m1 m2);;

(* ------------------------------------------------------------------------- *)
(* Pmapping and folding.                                                      *)
(* ------------------------------------------------------------------------- *)

let filter pred =
  let mpred (elt,()) = pred elt in
  fun (Set m) -> Set (Pmap.filter mpred m)
;;

let partition pred =
  let mpred (elt,()) = pred elt in
  fun (Set m) ->
    let (m1,m2) = Pmap.partition mpred m in
    (Set m1, Set m2)
;;

let app f =
  let mf (elt,()) = f elt in
  fun (Set m) -> Pmap.app mf m
;;

let foldl f =
  let mf (elt,(),acc) = f (elt,acc) in
  fun acc (Set m) -> Pmap.foldl mf acc m
;;

let foldr f =
  let mf (elt,(),acc) = f (elt,acc) in
  fun acc (Set m) -> Pmap.foldr mf acc m
;;

(* ------------------------------------------------------------------------- *)
(* Searching.                                                                *)
(* ------------------------------------------------------------------------- *)

let findl p =
  let mp (elt,()) = p elt in
  fun (Set m) ->
    match Pmap.findl mp m with
    | Some (elt,()) -> Some elt
    | None -> None
;;

let findr p =
  let mp (elt,()) = p elt in
  fun (Set m) ->
    match Pmap.findr mp m with
    | Some (elt,()) -> Some elt
    | None -> None
;;

let firstl f =
  let mf (elt,()) = f elt in
  fun (Set m) -> Pmap.firstl mf m
;;

let firstr f =
  let mf (elt,()) = f elt in
  fun (Set m) -> Pmap.firstr mf m
;;

let exists p =
  let mp (elt,()) = p elt in
  fun (Set m) -> Pmap.exists mp m
;;

let all p =
  let mp (elt,()) = p elt in
  fun (Set m) -> Pmap.all mp m
;;

let count p =
  let mp (elt,()) = p elt in
  fun (Set m) -> Pmap.count mp m
;;

(* ------------------------------------------------------------------------- *)
(* Comparing.                                                                *)
(* ------------------------------------------------------------------------- *)

let compareValue () () = Equal;;

let equalValue () () = true;;

let compare (Set m1) (Set m2) = Pmap.compare compareValue m1 m2;;

let equal (Set m1) (Set m2) = Pmap.equal equalValue m1 m2;;

let subset (Set m1) (Set m2) = Pmap.subsetDomain m1 m2;;

let disjoint (Set m1) (Set m2) = Pmap.disjointDomain m1 m2;;

(* ------------------------------------------------------------------------- *)
(* Converting to and from lists.                                             *)
(* ------------------------------------------------------------------------- *)

let transform f =
  let inc (x,l) = f x :: l in
  foldr inc []
;;

let toList (Set m) = Pmap.keys m;;

let fromList cmp elts = addList (empty cmp) elts;;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString set =
  "{" ^ (if null set then "" else Int.toString (size set)) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Iterators over sets                                                       *)
(* ------------------------------------------------------------------------- *)

type 'elt iterator = ('elt,unit) Pmap.iterator;;

let mkIterator (Set m) = Pmap.mkIterator m;;

let mkRevIterator (Set m) = Pmap.mkRevIterator m;;

let readIterator iter =
  let (elt,()) = Pmap.readIterator iter in
  elt
;;

let advanceIterator iter = Pmap.advanceIterator iter;;

end (* struct Pset *)
;;
