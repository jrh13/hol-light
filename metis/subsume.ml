(* ========================================================================= *)
(* SUBSUMPTION CHECKING FOR FIRST ORDER LOGIC CLAUSES                        *)
(* ========================================================================= *)

module Subsume = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let findRest pred =
  let rec f ys = function
    | [] -> None
    | (x :: xs) ->
        if pred x then Some (x, rev_append ys xs) else f (x :: ys) xs in
  f []
;;

let addSym (lit,acc) =
  match total Literal.sym lit with
  | None -> acc
  | Some lit -> lit :: acc
let clauseSym lits = List.foldl (curry addSym) lits lits;;


let sortClause cl =
  let lits = Literal.Set.toList cl in
  sortMap Literal.typedSymbols (revCompare Int.compare) lits
;;

let incompatible lit =
  let lits = clauseSym [lit] in
  fun lit' -> not (List.exists (can (Literal.unify Substitute.empty lit')) lits)
;;

(* ------------------------------------------------------------------------- *)
(* Clause ids and lengths.                                                   *)
(* ------------------------------------------------------------------------- *)

type clauseId = int;;

type clauseLength = int;;

type idSet = (clauseId * clauseLength) Pset.set;;

let idCompare (id1,len1) (id2,len2) =
  match Int.compare len1 len2 with
  | Less -> Less
  | Equal -> Int.compare id1 id2
  | Greater -> Greater;;

let idSetEmpty : idSet = Pset.empty idCompare;;

let idSetAdd (id_len,set) : idSet = Pset.add set id_len;;

let idSetAddMax max ((_,len) as id_len, set) : idSet =
  if len <= max then Pset.add set id_len else set;;

let idSetIntersect set1 set2 : idSet = Pset.intersect set1 set2;;

(* ------------------------------------------------------------------------- *)
(* A type of clause sets that supports efficient subsumption checking.       *)
(* ------------------------------------------------------------------------- *)

type 'a nonunit_t = Non_unit of {
  nextId : clauseId;
  clauses : (int, Literal.literal list * Thm.clause * 'a) Mmap.map;
  fstLits : (clauseId * clauseLength) Literal_net.literalNet;
  sndLits : (clauseId * clauseLength) Literal_net.literalNet
};;

type 'a subsume = Subsume of {
  empty : (Thm.clause * Substitute.subst * 'a) list;
  unitn : (Literal.literal * Thm.clause * 'a)  Literal_net.literalNet;
  nonunit : 'a nonunit_t
};;

let newSubsume () = Subsume {
  empty = [];
  unitn = Literal_net.newNet false;
  nonunit = Non_unit {
    nextId = 0;
    clauses = Intmap.newMap ();
    fstLits = Literal_net.newNet false;
    sndLits = Literal_net.newNet false}
};;

let size (Subsume {empty; unitn; nonunit}) =
  let Non_unit {clauses} = nonunit in
  length empty + Literal_net.size unitn + Intmap.size clauses;;

let insert (Subsume {empty; unitn; nonunit}) (cl',a) =
  match sortClause cl' with
  | [] ->
      let empty = (cl',Substitute.empty,a) :: empty in
      Subsume {empty = empty; unitn = unitn; nonunit = nonunit}
  | [lit] ->
      let unitn = Literal_net.insert unitn (lit,(lit,cl',a)) in
      Subsume {empty = empty; unitn = unitn; nonunit = nonunit}
  | fstLit :: (sndLit :: otherLits as nonFstLits) ->
      let Non_unit {nextId;clauses;fstLits;sndLits} = nonunit in
      let id_length = (nextId, Literal.Set.size cl') in
      let fstLits = Literal_net.insert fstLits (fstLit,id_length) in
      let (sndLit,otherLits) =
        match findRest (incompatible fstLit) nonFstLits with
        | Some sndLit_otherLits -> sndLit_otherLits
        | None -> (sndLit,otherLits) in
      let sndLits = Literal_net.insert sndLits (sndLit,id_length) in
      let lits' = otherLits @ [fstLit;sndLit] in
      let clauses = Intmap.insert clauses (nextId,(lits',cl',a)) in
      let nextId = nextId + 1 in
      let nonunit = Non_unit {nextId = nextId; clauses = clauses;
                             fstLits = fstLits; sndLits = sndLits} in
      Subsume {empty = empty; unitn = unitn; nonunit = nonunit}
;;

let filter pred (Subsume {empty; unitn; nonunit}) =
  let pred3 (_,_,x) = pred x in
  let empty = List.filter (fun _,_,x -> pred x) empty in
  let unitn = Literal_net.filter (fun _,_,x -> pred x) unitn in
  let nonunit =
    let Non_unit {nextId; clauses; fstLits; sndLits} = nonunit in
    let clauses' = Intmap.filter (fun x -> pred3 (snd x)) clauses in
    if Intmap.size clauses = Intmap.size clauses' then nonunit else
      let predId (id,_) = Intmap.inDomain id clauses' in
      let fstLits = Literal_net.filter predId fstLits
      and sndLits = Literal_net.filter predId sndLits in
      Non_unit {nextId = nextId; clauses = clauses'; fstLits = fstLits;
                sndLits = sndLits} in
  Subsume {empty = empty; unitn = unitn; nonunit = nonunit}
;;

let toString subsume = "Subsume{" ^ Int.toString (size subsume) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Subsumption checking.                                                     *)
(* ------------------------------------------------------------------------- *)

let matchLit lit' (lit,acc) =
  match total (Literal.matchLiterals Substitute.empty lit') lit with
  | Some sub -> sub :: acc
  | None -> acc;;

let genClauseSubsumes pred cl' lits' cl a =
  let rec mkSubsl acc sub = function
  | [] -> Some (sub, sortMap length Int.compare acc)
  | (lit' :: lits') ->
      match List.foldl (curry (matchLit lit')) [] cl with
      | [] -> None
      | [sub'] ->
          begin
            match total (Substitute.union sub) sub' with
            | None -> None
            | Some sub -> mkSubsl acc sub lits'
          end
      | subs -> mkSubsl (subs :: acc) sub lits' in
  let rec search = function
    | [] -> None
    | ((sub,[]) :: others) ->
        let x = (cl',sub,a) in
        if pred x then Some x else search others
    | ((_, [] :: _) :: others) -> search others
    | ((sub, (sub' :: subs) :: subsl) :: others) ->
        let others = (sub, subs :: subsl) :: others in
        match total (Substitute.union sub) sub' with
        | None -> search others
        | Some sub -> search ((sub,subsl) :: others) in
  match mkSubsl [] Substitute.empty lits' with
  | None -> None
  | Some sub_subsl -> search [sub_subsl]
;;

let emptySubsumes pred empty = List.find pred empty;;

let unitSubsumes pred unitn =
  let subLit lit =
    let subUnit (lit',cl',a) =
      match total (Literal.matchLiterals Substitute.empty lit') lit with
      | None -> None
      | Some sub ->
          let x = (cl',sub,a) in
          if pred x then Some x else None in
    first subUnit (Literal_net.matchNet unitn lit) in
  first subLit
;;

let nonunitSubsumes pred nonunit max cl =
  let addId = match max with
              | None -> idSetAdd
              | Some n -> idSetAddMax n in
  let subLit lits (lit,acc) =
    List.foldl (curry addId) acc (Literal_net.matchNet lits lit) in
  let Non_unit {clauses; fstLits; sndLits} = nonunit in
  let subCl' (id,_) =
    let (lits',cl',a) = Intmap.get clauses id in
    genClauseSubsumes pred cl' lits' cl a in
  let fstCands = List.foldl (curry (subLit fstLits)) idSetEmpty cl in
  let sndCands = List.foldl (curry (subLit sndLits)) idSetEmpty cl in
  let cands = idSetIntersect fstCands sndCands in
  Pset.firstl subCl' cands
;;

let genSubsumes pred (Subsume {empty; unitn; nonunit}) max cl =
  match emptySubsumes pred empty with
  | Some _ as s -> s
  | None ->
      if max = Some 0 then None else
        let cl = clauseSym (Literal.Set.toList cl) in
        match unitSubsumes pred unitn cl with
        | Some _ as s -> s
        | None ->
            if max = Some 1 then None
            else nonunitSubsumes pred nonunit max cl
;;

let subsumes pred subsume cl = genSubsumes pred subsume None cl;;

let strictlySubsumes pred subsume cl =
  genSubsumes pred subsume (Some (Literal.Set.size cl)) cl;;

let isSubsumed subs cl = Option.isSome (subsumes (kComb true) subs cl);;

let isStrictlySubsumed subs cl =
  Option.isSome (strictlySubsumes (kComb true) subs cl);;

(* ------------------------------------------------------------------------- *)
(* Single clause versions.                                                   *)
(* ------------------------------------------------------------------------- *)

let clauseSubsumes cl' cl =
  let lits' = sortClause cl'
  and lits = clauseSym (Literal.Set.toList cl) in
  match genClauseSubsumes (kComb true) cl' lits' lits () with
  | Some (_,sub,()) -> Some sub
  | None -> None
;;

let clauseStrictlySubsumes cl' cl =
  if Literal.Set.size cl' > Literal.Set.size cl then None
  else clauseSubsumes cl' cl;;

end (* struct Subsume *)
;;
