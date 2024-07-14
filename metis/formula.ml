(* ========================================================================= *)
(* FIRST ORDER LOGIC FORMULAS                                                *)
(* ========================================================================= *)

module Formula = struct

open Useful
open Order

(* ------------------------------------------------------------------------- *)
(* A type of first order logic formulas.                                     *)
(* ------------------------------------------------------------------------- *)

type formula =
  | True
  | False
  | Atom of Atom.atom
  | Not of formula
  | And of formula * formula
  | Or of formula * formula
  | Imp of formula * formula
  | Iff of formula * formula
  | Forall of Term.var * formula
  | Exists of Term.var * formula;;

(* ------------------------------------------------------------------------- *)
(* Constructors and destructors.                                             *)
(* ------------------------------------------------------------------------- *)

(* Booleans *)

let mkBoolean = function
  | true -> True
  | false -> False;;

let destBoolean =
  | function True -> true
  | False -> false
  | _ -> raise (Error "destBoolean");;

let isBoolean = can destBoolean;;

let isTrue fm =
  match fm with
  | True -> true
  | _ -> false;;

let isFalse fm =
  match fm with
  | False -> true
  | _ -> false;;

(* Functions *)

let functions fm =
  let rec funcs fs = function
    | [] -> fs
    | (True :: fms) -> funcs fs fms
    | (False :: fms) -> funcs fs fms
    | (Atom atm :: fms) -> funcs (Name_arity.Set.union (Atom.functions atm) fs) fms
    | (Not p :: fms) -> funcs fs (p :: fms)
    | (And (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> funcs fs (p :: fms)
    | (Exists (_,p) :: fms) -> funcs fs (p :: fms)
  in
    funcs Name_arity.Set.empty [fm];;

let functionNames fm =
  let rec funcs fs = function
      [] -> fs
    | (True :: fms) -> funcs fs fms
    | (False :: fms) -> funcs fs fms
    | (Atom atm :: fms) -> funcs (Name.Set.union (Atom.functionNames atm) fs) fms
    | (Not p :: fms) -> funcs fs (p :: fms)
    | (And (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> funcs fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> funcs fs (p :: fms)
    | (Exists (_,p) :: fms) -> funcs fs (p :: fms)
  in
    funcs Name.Set.empty [fm];;

(* Relations *)
let relations fm =
  let rec rels fs = function
      [] -> fs
    | (True :: fms) -> rels fs fms
    | (False :: fms) -> rels fs fms
    | (Atom atm :: fms) ->
      rels (Name_arity.Set.add fs (Atom.relation atm)) fms
    | (Not p :: fms) -> rels fs (p :: fms)
    | (And (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> rels fs (p :: fms)
    | (Exists (_,p) :: fms) -> rels fs (p :: fms)
  in rels Name_arity.Set.empty [fm];;


let relationNames fm =
  let rec rels fs = function
      [] -> fs
    | (True :: fms) -> rels fs fms
    | (False :: fms) -> rels fs fms
    | (Atom atm :: fms) -> rels (Name.Set.add fs (Atom.name atm)) fms
    | (Not p :: fms) -> rels fs (p :: fms)
    | (And (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Or (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Imp (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Iff (p,q) :: fms) -> rels fs (p :: q :: fms)
    | (Forall (_,p) :: fms) -> rels fs (p :: fms)
    | (Exists (_,p) :: fms) -> rels fs (p :: fms)
  in rels Name.Set.empty [fm];;

(* Atoms *)

let destAtom = function
    (Atom atm) -> atm
  | _ -> raise (Error "Formula.destAtom");;

let isAtom = can destAtom;;

(* Negations *)

let destNeg = function
    (Not p) -> p
  | _ -> raise (Error "Formula.destNeg");;

let isNeg = can destNeg;;

let stripNeg =
    let rec strip n = function
          (Not fm) -> strip (n + 1) fm
        | fm -> (n,fm)
    in
      strip 0
    ;;

(* Conjunctions *)

let listMkConj fms =
    match List.rev fms with
      [] -> True
    | fm :: fms -> Mlist.foldl (fun (x, y) -> And (x, y)) fm fms;;

let stripConj =
  let rec strip cs = function
      (And (p,q)) -> strip (p :: cs) q
    | fm -> List.rev (fm :: cs)
  in function
      True -> []
    | fm -> strip [] fm;;

let flattenConj =
      let rec flat acc = function
          [] -> acc
        | (And (p,q) :: fms) -> flat acc (q :: p :: fms)
        | (True :: fms) -> flat acc fms
        | (fm :: fms) -> flat (fm :: acc) fms
    in
      fun fm -> flat [] [fm]
    ;;

(* Disjunctions *)

let listMkDisj fms =
    match List.rev fms with
      [] -> False
    | fm :: fms -> Mlist.foldl (fun (x,y) -> Or (x,y)) fm fms;;

let stripDisj =
  let rec strip cs = function
      (Or (p,q)) -> strip (p :: cs) q
    | fm -> List.rev (fm :: cs)
  in function
      False -> []
    | fm -> strip [] fm;;

let flattenDisj =
      let rec flat acc = function
          [] -> acc
        | (Or (p,q) :: fms) -> flat acc (q :: p :: fms)
        | (False :: fms) -> flat acc fms
        | (fm :: fms) -> flat (fm :: acc) fms
    in
      fun fm -> flat [] [fm]
    ;;

(* Equivalences *)

let listMkEquiv fms =
    match List.rev fms with
      [] -> True
    | fm :: fms -> Mlist.foldl (fun (x,y) -> Iff (x,y)) fm fms;;

let stripEquiv =
  let rec strip cs = function
      (Iff (p,q)) -> strip (p :: cs) q
    | fm -> List.rev (fm :: cs)
  in function
      True -> []
    | fm -> strip [] fm;;

let flattenEquiv =
      let rec flat acc = function
          [] -> acc
        | (Iff (p,q) :: fms) -> flat acc (q :: p :: fms)
        | (True :: fms) -> flat acc fms
        | (fm :: fms) -> flat (fm :: acc) fms
    in
      fun fm -> flat [] [fm]
    ;;

(* Universal quantifiers *)

let destForall = function
    (Forall (v,f)) -> (v,f)
  | _ -> raise (Error "destForall");;

let isForall = can destForall;;

let rec listMkForall = function
    ([],body) -> body
  | (v :: vs, body) -> Forall (v, listMkForall (vs,body));;

let setMkForall (vs,body) = Name.Set.foldr (fun (x,y) -> Forall (x,y)) body vs;;

let stripForall =
  let rec strip vs = function
      (Forall (v,b)) -> strip (v :: vs) b
    | tm -> (List.rev vs, tm)
  in
    strip [];;

(* Existential quantifiers *)

let destExists = function
    (Exists (v,f)) -> (v,f)
  | _ -> raise (Error "destExists");;

let isExists = can destExists;;

let rec listMkExists = function
    ([],body) -> body
  | (v :: vs, body) -> Exists (v, listMkExists (vs,body));;

let setMkExists (vs,body) = Name.Set.foldr (fun (x,y) -> Exists (x,y)) body vs;;

let stripExists =
  let rec strip vs = function
      (Exists (v,b)) -> strip (v :: vs) b
    | tm -> (List.rev vs, tm)
  in
    strip [];;

(* ------------------------------------------------------------------------- *)
(* The size of a formula in symbols.                                         *)
(* ------------------------------------------------------------------------- *)

let symbols fm =
  let rec sz n = function
      [] -> n
    | (True :: fms) -> sz (n + 1) fms
    | (False :: fms) -> sz (n + 1) fms
    | (Atom atm :: fms) -> sz (n + Atom.symbols atm) fms
    | (Not p :: fms) -> sz (n + 1) (p :: fms)
    | (And (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Or (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Imp (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Iff (p,q) :: fms) -> sz (n + 1) (p :: q :: fms)
    | (Forall (_,p) :: fms) -> sz (n + 1) (p :: fms)
    | (Exists (_,p) :: fms) -> sz (n + 1) (p :: fms)
in
  sz 0 [fm];;

(* ------------------------------------------------------------------------- *)
(* A total comparison function for formulas.                                 *)
(* ------------------------------------------------------------------------- *)

let compare fm1_fm2 =
  let rec cmp = function
      [] -> Equal
    | (f1_f2 :: fs) ->
      if Portable.pointerEqual f1_f2 then cmp fs
      else
        match f1_f2 with
          (True,True) -> cmp fs
        | (True,_) -> Less
        | (_,True) -> Greater
        | (False,False) -> cmp fs
        | (False,_) -> Less
        | (_,False) -> Greater
        | (Atom atm1, Atom atm2) ->
          (match Atom.compare (atm1,atm2) with
             Less -> Less
           | Equal -> cmp fs
           | Greater -> Greater)
        | (Atom _, _) -> Less
        | (_, Atom _) -> Greater
        | (Not p1, Not p2) -> cmp ((p1,p2) :: fs)
        | (Not _, _) -> Less
        | (_, Not _) -> Greater
        | (And (p1,q1), And (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (And _, _) -> Less
        | (_, And _) -> Greater
        | (Or (p1,q1), Or (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Or _, _) -> Less
        | (_, Or _) -> Greater
        | (Imp (p1,q1), Imp (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Imp _, _) -> Less
        | (_, Imp _) -> Greater
        | (Iff (p1,q1), Iff (p2,q2)) -> cmp ((p1,p2) :: (q1,q2) :: fs)
        | (Iff _, _) -> Less
        | (_, Iff _) -> Greater
        | (Forall (v1,p1), Forall (v2,p2)) ->
          (match Name.compare (v1,v2) with
             Less -> Less
           | Equal -> cmp ((p1,p2) :: fs)
           | Greater -> Greater)
        | (Forall _, Exists _) -> Less
        | (Exists _, Forall _) -> Greater
        | (Exists (v1,p1), Exists (v2,p2)) ->
          (match Name.compare (v1,v2) with
             Less -> Less
           | Equal -> cmp ((p1,p2) :: fs)
           | Greater -> Greater)
in
  cmp [fm1_fm2];;

let equal fm1 fm2 = compare (fm1,fm2) = Equal;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v =
      let rec f = function
          [] -> false
        | (True :: fms) -> f fms
        | (False :: fms) -> f fms
        | (Atom atm :: fms) -> Atom.freeIn v atm || f fms
        | (Not p :: fms) -> f (p :: fms)
        | (And (p,q) :: fms) -> f (p :: q :: fms)
        | (Or (p,q) :: fms) -> f (p :: q :: fms)
        | (Imp (p,q) :: fms) -> f (p :: q :: fms)
        | (Iff (p,q) :: fms) -> f (p :: q :: fms)
        | (Forall (w,p) :: fms) ->
          if Name.equal v w then f fms else f (p :: fms)
        | (Exists (w,p) :: fms) ->
          if Name.equal v w then f fms else f (p :: fms)
    in
      fun fm -> f [fm]
    ;;

let add (fm,vs) =
  let rec fv vs = function
      [] -> vs
    | ((_,True) :: fms) -> fv vs fms
    | ((_,False) :: fms) -> fv vs fms
    | ((bv, Atom atm) :: fms) ->
      fv (Name.Set.union vs (Name.Set.difference (Atom.freeVars atm) bv)) fms
    | ((bv, Not p) :: fms) -> fv vs ((bv,p) :: fms)
    | ((bv, And (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Or (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Imp (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Iff (p,q)) :: fms) -> fv vs ((bv,p) :: (bv,q) :: fms)
    | ((bv, Forall (v,p)) :: fms) -> fv vs ((Name.Set.add bv v, p) :: fms)
    | ((bv, Exists (v,p)) :: fms) -> fv vs ((Name.Set.add bv v, p) :: fms)

   in fv vs [(Name.Set.empty,fm)];;

  let freeVars fm = add (fm,Name.Set.empty);;

  let freeVarsList fms = Mlist.foldl add Name.Set.empty fms;;

let specialize fm = snd (stripForall fm);;

let generalize fm = listMkForall (Name.Set.toList (freeVars fm), fm);;

(* ------------------------------------------------------------------------- *)
(* Substitutions.                                                            *)
(* ------------------------------------------------------------------------- *)

  let rec substCheck sub fm = if Substitute.null sub then fm else substFm sub fm

  and substFm sub fm = match fm with
        True -> fm
      | False -> fm
      | Atom (p,tms) ->
          let tms' = Sharing.map (Substitute.subst sub) tms
        in
          if Portable.pointerEqual (tms,tms') then fm else Atom (p,tms')
      | Not p ->
          let p' = substFm sub p
        in
          if Portable.pointerEqual (p,p') then fm else Not p'
      | And (p,q) -> substConn sub fm (fun (x,y) -> And (x,y)) p q
      | Or (p,q) -> substConn sub fm (fun (x,y) -> Or (x,y)) p q
      | Imp (p,q) -> substConn sub fm (fun (x,y) -> Imp (x,y)) p q
      | Iff (p,q) -> substConn sub fm (fun (x,y) -> Iff (x,y)) p q
      | Forall (v,p) -> substQuant sub fm (fun (x,y) -> Forall (x,y)) v p
      | Exists (v,p) -> substQuant sub fm (fun (x,y) -> Exists (x,y)) v p

  and substConn sub fm conn p q =
        let p' = substFm sub p
        and q' = substFm sub q
      in
        if Portable.pointerEqual (p,p') &&
           Portable.pointerEqual (q,q')
        then fm
        else conn (p',q')

  and substQuant sub fm quant v p =
        let v' =
              let f (w,s) =
                  if Name.equal w v then s
                  else
                    match Substitute.peek sub w with
                      None -> Name.Set.add s w
                    | Some tm -> Name.Set.union s (Term.freeVars tm)

              in let vars = freeVars p
              in let vars = Name.Set.foldl f Name.Set.empty vars
            in
              Term.variantPrime vars v

        in let sub =
            if Name.equal v v' then Substitute.remove sub (Name.Set.singleton v)
            else Substitute.insert sub (v, Term.Var v')

        in let p' = substCheck sub p
      in
        if Name.equal v v' && Portable.pointerEqual (p,p') then fm
        else quant (v',p');;

  let subst = substCheck;;

(* ------------------------------------------------------------------------- *)
(* The equality relation.                                                    *)
(* ------------------------------------------------------------------------- *)

let mkEq a_b = Atom (Atom.mkEq a_b);;

let destEq fm = Atom.destEq (destAtom fm);;

let isEq = can destEq;;

let mkNeq a_b = Not (mkEq a_b);;

let destNeq = function
    (Not fm) -> destEq fm
  | _ -> raise (Error "Formula.destNeq");;

let isNeq = can destNeq;;

let mkRefl tm = Atom (Atom.mkRefl tm);;

let destRefl fm = Atom.destRefl (destAtom fm);;

let isRefl = can destRefl;;

let sym fm = Atom (Atom.sym (destAtom fm));;

let lhs fm = fst (destEq fm);;

let rhs fm = snd (destEq fm);;

(* ------------------------------------------------------------------------- *)
(* Parsing and pretty-printing.                                              *)
(* ------------------------------------------------------------------------- *)

let truthName = Name.fromString "T"
and falsityName = Name.fromString "F"
and conjunctionName = Name.fromString "/\\"
and disjunctionName = Name.fromString "\\/"
and implicationName = Name.fromString "==>"
and equivalenceName = Name.fromString "<=>"
and universalName = Name.fromString "!"
and existentialName = Name.fromString "?";;

  let rec demote = function
      True -> Term.Fn (truthName,[])
    | False -> Term.Fn (falsityName,[])
    | (Atom (p,tms)) -> Term.Fn (p,tms)
    | (Not p) ->
      let
        s = "~"
      in
        Term.Fn (Name.fromString s, [demote p])
    | (And (p,q)) -> Term.Fn (conjunctionName, [demote p; demote q])
    | (Or (p,q)) -> Term.Fn (disjunctionName, [demote p; demote q])
    | (Imp (p,q)) -> Term.Fn (implicationName, [demote p; demote q])
    | (Iff (p,q)) -> Term.Fn (equivalenceName, [demote p; demote q])
    | (Forall (v,b)) -> Term.Fn (universalName, [Term.Var v; demote b])
    | (Exists (v,b)) ->
      Term.Fn (existentialName, [Term.Var v; demote b]);;

  let toString fm = Term.toString (demote fm);;


(* ------------------------------------------------------------------------- *)
(* Splitting goals.                                                          *)
(* ------------------------------------------------------------------------- *)

  let add_asms asms goal =
      if Mlist.null asms then goal else Imp (listMkConj (List.rev asms), goal);;

  let add_var_asms asms v goal = add_asms asms (Forall (v,goal));;

  let rec split asms pol fm =
      match (pol,fm) with
        (* Positive splittables *)
        (true,True) -> []
      | (true, Not f) -> split asms false f
      | (true, And (f1,f2)) -> split asms true f1 @ split (f1 :: asms) true f2
      | (true, Or (f1,f2)) -> split (Not f1 :: asms) true f2
      | (true, Imp (f1,f2)) -> split (f1 :: asms) true f2
      | (true, Iff (f1,f2)) ->
        split (f1 :: asms) true f2 @ split (f2 :: asms) true f1
      | (true, Forall (v,f)) -> List.map (add_var_asms asms v) (split [] true f)
        (* Negative splittables *)
      | (false,False) -> []
      | (false, Not f) -> split asms true f
      | (false, And (f1,f2)) -> split (f1 :: asms) false f2
      | (false, Or (f1,f2)) ->
        split asms false f1 @ split (Not f1 :: asms) false f2
      | (false, Imp (f1,f2)) -> split asms true f1 @ split (f1 :: asms) false f2
      | (false, Iff (f1,f2)) ->
        split (f1 :: asms) false f2 @ split (Not f2 :: asms) true f1
      | (false, Exists (v,f)) -> List.map (add_var_asms asms v) (split [] false f)
        (* Unsplittables *)
      | _ -> [add_asms asms (if pol then fm else Not fm)];;

  let splitGoal fm = split [] true fm;;

module Ordered =
struct type t = formula let compare = fromCompare compare end

module Map = Mmap.Make (Ordered);;

module Set = Mset.Make (Ordered);;

end
