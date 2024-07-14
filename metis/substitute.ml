(* ========================================================================= *)
(* FIRST ORDER LOGIC SUBSTITUTIONS                                           *)
(* ========================================================================= *)

module Substitute = struct

open Useful

(* ------------------------------------------------------------------------- *)
(* A type of first order logic substitutions.                                *)
(* ------------------------------------------------------------------------- *)

type subst = Subst of Term.term Name.Map.map;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let empty = Subst (Name.Map.newMap ());;

let null (Subst m) = Name.Map.null m;;

let size (Subst m) = Name.Map.size m;;

let peek (Subst m) v = Name.Map.peek m v;;

let insert (Subst m) v_tm = Subst (Name.Map.insert m v_tm);;

let singleton v_tm = insert empty v_tm;;

let toList (Subst m) = Name.Map.toList m;;

let fromList l = Subst (Name.Map.fromList l);;

let foldl f b (Subst m) = Name.Map.foldl f b m;;

let foldr f b (Subst m) = Name.Map.foldr f b m;;


(* ------------------------------------------------------------------------- *)
(* Normalizing removes identity substitutions.                               *)
(* ------------------------------------------------------------------------- *)

let normalize (Subst m as sub) =
  let isNotId (v, tm) = not (Term.equalVar v tm) in
  let m' = Name.Map.filter isNotId m
  in if Name.Map.size m = Name.Map.size m' then sub else Subst m'
;;

(* ------------------------------------------------------------------------- *)
(* Applying a substitution to a first order logic term.                      *)
(* ------------------------------------------------------------------------- *)

let subst sub =
  let rec tmSub = function
        (Term.Var v as tm) ->
          (match peek sub v with
             Some tm' -> if Portable.pointerEqual (tm,tm') then tm else tm'
           | None -> tm)
      | (Term.Fn (f,args) as tm) ->
          let args' = Sharing.map tmSub args
          in
            if Portable.pointerEqual (args,args') then tm
            else Term.Fn (f,args')
    in
      fun tm -> if null sub then tm else tmSub tm
    ;;

(* ------------------------------------------------------------------------- *)
(* Restricting a substitution to a given set of variables.                   *)
(* ------------------------------------------------------------------------- *)

let restrict (Subst m as sub) varSet =
      let isRestrictedVar (v, _) = Name.Set.member v varSet in
      let m' = Name.Map.filter isRestrictedVar m
    in
      if Name.Map.size m = Name.Map.size m' then sub else Subst m'
    ;;

let remove (Subst m as sub) varSet =
      let isRestrictedVar (v, _) = not (Name.Set.member v varSet) in
      let m' = Name.Map.filter isRestrictedVar m
    in
      if Name.Map.size m = Name.Map.size m' then sub else Subst m'
    ;;

(* ------------------------------------------------------------------------- *)
(* Composing two substitutions so that the following identity holds:         *)
(*                                                                           *)
(* subst (compose sub1 sub2) tm = subst sub2 (subst sub1 tm)                 *)
(* ------------------------------------------------------------------------- *)

let compose (Subst m1 as sub1) sub2 =
      let f (v,tm,s) = insert s (v, subst sub2 tm)
    in
      if null sub2 then sub1 else Name.Map.foldl f sub2 m1
    ;;

(* ------------------------------------------------------------------------- *)
(* Creating the union of two compatible substitutions.                       *)
(* ------------------------------------------------------------------------- *)

let union (Subst m1 as s1) (Subst m2 as s2) =
  let compatible ((_,tm1),(_,tm2)) =
      if Term.equal tm1 tm2 then Some tm1
      else raise (Error "Substitute.union: incompatible")
  in
      if Name.Map.null m1 then s2
      else if Name.Map.null m2 then s1
      else Subst (Name.Map.union compatible m1 m2)
;;

(* ------------------------------------------------------------------------- *)
(* Substitutions can be inverted iff they are renaming substitutions.        *)
(* ------------------------------------------------------------------------- *)

let invert (Subst m) =
  let inv = function
      (v, Term.Var w, s) ->
      if Name.Map.inDomain w s then raise (Error "Substitute.invert: non-injective")
      else Name.Map.insert s (w, Term.Var v)
    | (_, Term.Fn _, _) -> raise (Error "Substitute.invert: non-variable")
  in Subst (Name.Map.foldl inv (Name.Map.newMap ()) m)
;;

let isRenaming = can invert;;

(* ------------------------------------------------------------------------- *)
(* Creating a substitution to freshen variables.                             *)
(* ------------------------------------------------------------------------- *)

let freshVars s =
    let add (v, m) = insert m (v, Term.newVar ())
    in
      Name.Set.foldl add empty s
    ;;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let redexes =
    let add (v,_,s) = Name.Set.add s v
    in
      foldl add Name.Set.empty
    ;;

let residueFreeVars =
    let add (_,t,s) = Name.Set.union s (Term.freeVars t)
    in
      foldl add Name.Set.empty
    ;;

let freeVars =
    let add (v,t,s) = Name.Set.union (Name.Set.add s v) (Term.freeVars t)
    in
      foldl add Name.Set.empty
    ;;

(* ------------------------------------------------------------------------- *)
(* Functions.                                                                *)
(* ------------------------------------------------------------------------- *)

let functions =
    let add (_,t,s) = Name_arity.Set.union s (Term.functions t)
    in
      foldl add Name_arity.Set.empty
    ;;

(* ------------------------------------------------------------------------- *)
(* Matching for first order logic terms.                                     *)
(* ------------------------------------------------------------------------- *)

let matchTerms sub tm1 tm2 =
  let rec matchList sub = function
      [] -> sub
    | ((Term.Var v, tm) :: rest) ->
        let sub =
            match peek sub v with
              None -> insert sub (v,tm)
            | Some tm' ->
              if Term.equal tm tm' then sub
              else raise (Error "Substitute.match: incompatible matches")
      in
        matchList sub rest
    | ((Term.Fn (f1,args1), Term.Fn (f2,args2)) :: rest) ->
      if Name.equal f1 f2 && length args1 = length args2 then
        matchList sub (zip args1 args2 @ rest)
      else raise (Error "Substitute.match: different structure")
    | _ -> raise (Error "Substitute.match: functions can't match vars")
  in matchList sub [(tm1,tm2)]
;;

(* ------------------------------------------------------------------------- *)
(* Unification for first order logic terms.                                  *)
(* ------------------------------------------------------------------------- *)

let unify sub tm1 tm2 =
  let rec solve sub = function
      [] -> sub
    | (((tm1,tm2) as tm1_tm2) :: rest) ->
      if Portable.pointerEqual tm1_tm2 then solve sub rest
      else solve' sub (subst sub tm1, subst sub tm2, rest)

  and solve' sub = function
      ((Term.Var v), tm, rest) ->
      if Term.equalVar v tm then solve sub rest
      else if Term.freeIn v tm then raise (Error "Substitute.unify: occurs check")
      else
        (match peek sub v with
           None -> solve (compose sub (singleton (v,tm))) rest
         | Some tm' -> solve' sub (tm', tm, rest))
    | (tm1, ((Term.Var _) as tm2), rest) -> solve' sub (tm2, tm1, rest)
    | (Term.Fn (f1,args1), Term.Fn (f2,args2), rest) ->
      if Name.equal f1 f2 && length args1 = length args2 then
        solve sub (zip args1 args2 @ rest)
      else
        raise (Error "Substitute.unify: different structure")

  in solve sub [(tm1,tm2)];;

end


