(* ========================================================================= *)
(* NAMES                                                                     *)
(* ========================================================================= *)

module Name = struct

(* ------------------------------------------------------------------------- *)
(* A type of names.                                                          *)
(* ------------------------------------------------------------------------- *)

type name = string;;
let pp_name s = pp_string s;;

(* ------------------------------------------------------------------------- *)
(* A total ordering.                                                         *)
(* ------------------------------------------------------------------------- *)

let compare = String.compare;;

let equal n1 n2 = n1 = n2;;

(* ------------------------------------------------------------------------- *)
(* Fresh variables.                                                          *)
(* ------------------------------------------------------------------------- *)

let prefix  = "_";;
let numName i = mkPrefix prefix (Int.toString i);;
let newName () = numName (newInt ());;
let newNames n = List.map numName (newInts n);;

let variantPrime avoid =
  let rec variant n = if avoid n then variant (n ^ "'") else n in
  variant;;

let isDigit c =
  Char.(<=) '0' c && Char.(<=) c '9';;

let variantNum avoid n =
  let isDigitOrPrime c = c = '\'' || isDigit c in
  if not (avoid n) then n
  else
    let n = stripSuffix isDigitOrPrime n in
    let rec variant i =
      let n_i = n ^ Int.toString i in
      if avoid n_i then variant (i + 1) else n_i in
    variant 0
;;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty printing.                                              *)
(* ------------------------------------------------------------------------- *)

let toString s : string = s;;

let fromString s : name = s;;

module Map = struct
let newMap () = Mmap.newMap compare ();;
let singleton kv = Mmap.singleton compare kv;;
let fromList xs = Mmap.fromList compare xs;;
let mapPartial f m = Mmap.mapPartial compare f m;;
let null = Mmap.null and size = Mmap.size and get = Mmap.get
and peek = Mmap.peek and insert = Mmap.insert and toList = Mmap.toList
and foldl = Mmap.foldl and foldr = Mmap.foldr and filter = Mmap.filter
and inDomain = Mmap.inDomain and union = Mmap.union and delete = Mmap.delete
and transform = Mmap.transform and exists = Mmap.exists;;
end (* struct Map *)
;;

module Set = struct
let empty : name Mset.set = Mset.empty compare;;
let singleton k = Mset.singleton compare k;;
let intersect m1 m2 = Mset.intersect compare;;
let intersectList = Mset.intersectList compare;;
let fromList = Mset.fromList compare;;
let add = Mset.add and foldr = Mset.foldr and foldl = Mset.foldl
and member = Mset.member and union = Mset.union and difference = Mset.difference
and toList = Mset.toList and null = Mset.null and size = Mset.size
and pick = Mset.pick and equal = Mset.equal and exists = Mset.exists
and delete = Mset.delete and subset = Mset.subset and findl = Mset.findl
and firstl = Mset.firstl and transform = Mset.transform and all = Mset.all
and count = Mset.count;;
end (* struct Set *)
;;

end (* struct Name *)
;;
