(* ========================================================================= *)
(* NAME/ARITY PAIRS                                                          *)
(* ========================================================================= *)

module Name_arity = struct

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

let compare (n1,i1) (n2,i2) =
  match Name.compare n1 n2 with
  | Less -> Less
  | Equal -> Int.compare i1 i2
  | Greater -> Greater;;

let equal (n1,i1) (n2,i2) = i1 = i2 && Name.equal n1 n2;;

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
let compose m1 m2 =
  let pk ((_,a), n) = peek m2 (n, a) in
  mapPartial pk m1
;;
end (* struct Map *)
;;

module Set = struct
let empty : nameArity Mset.set = Mset.empty compare;;
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
let allNullary = all nullary
;;
end (* struct Set *)
;;
end (* struct Name_arity *)
;;
