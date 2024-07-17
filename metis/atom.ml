(* ========================================================================= *)
(* FIRST ORDER LOGIC ATOMS                                                   *)
(* ========================================================================= *)

module Atom = struct

(* ------------------------------------------------------------------------- *)
(* A type for storing first order logic atoms.                               *)
(* ------------------------------------------------------------------------- *)

type relationName = Name.name;;

type relation = relationName * int;;

type atom = relationName * Term.term list;;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

let name ((rel,_) : atom) = rel;;

let arguments ((_,args) : atom) = args;;

let arity atm = length (arguments atm);;

let relation atm = (name atm, arity atm);;

let functions =
  let f tm acc = Name_arity.Set.union (Term.functions tm) acc in
  fun atm -> List.foldl f Name_arity.Set.empty (arguments atm)
;;

let functionNames =
  let f tm acc = Name.Set.union (Term.functionNames tm) acc in
  fun atm -> List.foldl f Name.Set.empty (arguments atm)
;;

(* Binary relations *)

let mkBinop p (a,b) : atom = (p,[a;b])
;;

let destBinop p =
  function
  | (x,[a;b]) -> if Name.equal x p then (a,b)
                 else raise (Error "Atom.destBinop: wrong binop")
  | _ -> raise (Error "Atom.destBinop: not a binop");;

let isBinop p = can (destBinop p)
;;

(* ------------------------------------------------------------------------- *)
(* The size of an atom in symbols.                                           *)
(* ------------------------------------------------------------------------- *)

let symbols atm =
  List.foldl (fun tm z -> Term.symbols tm + z) 1 (arguments atm)
;;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for atoms.                                    *)
(* ------------------------------------------------------------------------- *)

let compare (p1,tms1) (p2,tms2) =
  match Name.compare p1 p2 with
  | Less -> Less
  | Equal -> lexCompare Term.compare tms1 tms2
  | Greater -> Greater
;;

let equal atm1 atm2 = compare atm1 atm2 = Equal
;;

(* ------------------------------------------------------------------------- *)
(* Subterms.                                                                 *)
(* ------------------------------------------------------------------------- *)

let subterm x y =
  match x, y with
  | (_, []) -> raise (Bug "Atom.subterm: empty path")
  | ((_,tms), h :: t) ->
      if h >= length tms then raise (Error "Atom.subterm: bad path")
      else Term.subterm (List.nth tms h) t;;

let subterms ((_,tms) : atom) =
  let f (n,tm) l =
    List.map (fun (p,s) -> (n :: p, s)) (Term.subterms tm) @ l in
  List.foldl f [] (enumerate tms)
;;

let replace ((rel,tms) as atm) =
  function
  | ([],_) -> raise (Bug "Atom.replace: empty path")
  | (h :: t, res) ->
      if h >= length tms then
        raise (Error "Atom.replace: bad path")
      else
        let tm = List.nth tms h in
        let tm' = Term.replace tm (t,res) in
        if Portable.pointerEqual (tm,tm') then
          atm
        else (rel, updateNth (h,tm') tms)
;;

let find pred =
  let f (i,tm) =
    match Term.find pred tm with
    | Some path -> Some (i :: path)
    | None -> None in
  fun (_,tms) -> first f (enumerate tms)
;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v atm = List.exists (Term.freeIn v) (arguments atm);;

let freeVars =
  let f tm acc = Name.Set.union (Term.freeVars tm) acc in
  fun atm -> List.foldl f Name.Set.empty (arguments atm)
;;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

let subst sub ((p,tms) as atm) : atom =
  let tms' = Sharing.map (Substitute.subst sub) tms in
  if Portable.pointerEqual (tms',tms) then atm else (p,tms')
;;

(* ------------------------------------------------------------------------- *)
(* Matching.                                                                 *)
(* ------------------------------------------------------------------------- *)

let matchAtoms sub (p1,tms1) (p2,tms2) =
  let matchArg (tm1,tm2) sub = Substitute.matchTerms sub tm1 tm2 in
  let _ = (Name.equal p1 p2 && length tms1 = length tms2) ||
          raise (Error "Atom.match") in
  List.foldl matchArg sub (zip tms1 tms2)
;;

(* ------------------------------------------------------------------------- *)
(* Unification.                                                              *)
(* ------------------------------------------------------------------------- *)

let unify sub (p1,tms1) (p2,tms2) =
  let unifyArg (tm1,tm2) sub = Substitute.unify sub tm1 tm2 in
  let _ = (Name.equal p1 p2 && length tms1 = length tms2) ||
          raise (Error "Atom.unify") in
  List.foldl unifyArg sub (zip tms1 tms2)
;;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

let eqRelationName = Name.fromString "=";;

let eqRelationArity = 2;;

let eqRelation = (eqRelationName,eqRelationArity);;

let mkEq = mkBinop eqRelationName;;

let destEq x = destBinop eqRelationName x;;

let isEq x = isBinop eqRelationName x;;

let mkRefl tm = mkEq (tm,tm);;

let destRefl atm =
  let (l,r) = destEq atm in
  let _ = Term.equal l r || raise (Error "Atom.destRefl") in
  l
;;

let isRefl x = can destRefl x;;

let sym atm =
  let (l,r) = destEq atm in
  let _ = not (Term.equal l r) || raise (Error "Atom.sym: refl") in
  mkEq (r,l)
;;

let lhs atm = fst (destEq atm);;

let rhs atm = snd (destEq atm);;

(* ------------------------------------------------------------------------- *)
(* Special support for terms with type annotations.                          *)
(* ------------------------------------------------------------------------- *)

let typedSymbols ((_,tms) : atom) =
  List.foldl (fun tm z -> Term.typedSymbols tm + z) 1 tms;;

let nonVarTypedSubterms (_,tms) =
  let addArg (n,arg) acc =
    let addTm (path,tm) acc = (n :: path, tm) :: acc in
    List.foldl addTm acc (Term.nonVarTypedSubterms arg) in
  List.foldl addArg [] (enumerate tms)
;;

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
let empty : atom Mset.set = Mset.empty compare;;
let singleton k = Mset.singleton compare k;;
let intersect m1 m2 = Mset.intersect compare;;
let intersectList = Mset.intersectList compare;;
let add = Mset.add and foldr = Mset.foldr and foldl = Mset.foldl
and member = Mset.member and union = Mset.union and difference = Mset.difference
and toList = Mset.toList and null = Mset.null and size = Mset.size
and pick = Mset.pick and equal = Mset.equal and exists = Mset.exists
and fromList = Mset.fromList and delete = Mset.delete and subset = Mset.subset
and findl = Mset.findl and firstl = Mset.firstl and transform = Mset.transform
and all = Mset.all and count = Mset.count;;
end (* struct Set *)
;;

end (* struct Atom *)
;;
