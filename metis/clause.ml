(* ========================================================================= *)
(* CLAUSE = ID + THEOREM                                                     *)
(* ========================================================================= *)

module Clause = struct

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let newId =
  let r = ref 0 in
  let newI () =
    let n = !r in
    let () = r := n + 1 in
    n in
  fun () -> Portable.critical newI ()
;;

(* ------------------------------------------------------------------------- *)
(* A type of clause.                                                         *)
(* ------------------------------------------------------------------------- *)

type literalOrder =
  | No_literal_order
  | Unsigned_literal_order
  | Positive_literal_order;;

type parameters = Parameters of {
  ordering : Knuth_bendix_order.kbo;
  orderLiterals : literalOrder;
  orderTerms : bool
};;

type clauseId = int;;

type clause = Clause of {
    parameters : parameters;
    id : clauseId;
    thm : Thm.thm
};;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString (Clause {thm}) = Thm.toString thm;;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let default = Parameters {
  ordering = Knuth_bendix_order.default;
  orderLiterals = Positive_literal_order;
  orderTerms = true
};;

let mk p i t = Clause {parameters = p; id = i; thm = t};;

let equalThms cl cl' = Thm.equal cl.Clause.thm cl'.Clause.thm;;

let newClause parameters thm =
    Clause {parameters = parameters; id = newId (); thm = thm};;

let literals cl = Thm.clause cl.Clause.thm;;

let isTautology (Clause {thm}) = Thm.isTautology thm;;

let isContradiction (Clause {thm}) = Thm.isContradiction thm;;

(* ------------------------------------------------------------------------- *)
(* The term ordering is used to cut down inferences.                         *)
(* ------------------------------------------------------------------------- *)

let strictlyLess ordering x_y =
  match Knuth_bendix_order.compare ordering x_y with
  | Some (Less) -> true
  | _ -> false;;

let isLargerTerm (Parameters {ordering; orderTerms}) l_r =
  not orderTerms || not (strictlyLess ordering l_r)
;;

let atomToTerms atm =
  match total Atom.destEq atm with
  | None -> [Term.Fn atm]
  | Some (l,r) -> [l;r]
;;

let notStrictlyLess ordering (xs,ys) =
  let less x = List.exists (fun y -> strictlyLess ordering (x,y)) ys in
  not (List.all less xs)
;;

let isLargerLiteral (Parameters {ordering; orderLiterals}) lits =
  match orderLiterals with
  | No_literal_order -> kComb true
  | Unsigned_literal_order ->
      let addLit ((_,atm),acc) = atomToTerms atm @ acc in
      let tms = Literal.Set.foldl addLit [] lits in
      fun (_,atm') -> notStrictlyLess ordering (atomToTerms atm', tms)
  | Positive_literal_order ->
      match Literal.Set.findl (kComb true) lits with
      | None -> kComb true
      | Some (pol,_) ->
          let addLit ((p,atm),acc) =
            if p = pol then atomToTerms atm @ acc else acc in
          let tms = Literal.Set.foldl addLit [] lits in
          fun (pol',atm') ->
            if pol <> pol' then pol
            else notStrictlyLess ordering (atomToTerms atm', tms)
;;

let largestLiterals (Clause {parameters; thm}) =
  let litSet = Thm.clause thm in
  let isLarger = isLargerLiteral parameters litSet in
  let addLit (lit,s) = if isLarger lit then Literal.Set.add s lit else s in
  Literal.Set.foldr addLit Literal.Set.empty litSet
;;

let largestEquations cl =
  let Clause {parameters} = cl in
  let addEq lit ort ((l,_) as l_r) acc =
    if isLargerTerm parameters l_r then (lit,ort,l) :: acc else acc in
  let addLit (lit,acc) =
    match total Literal.destEq lit with
    | None -> acc
    | Some (l,r) ->
        let acc = addEq lit Rewrite.Right_to_left (r,l) acc in
        let acc = addEq lit Rewrite.Left_to_right (l,r) acc in
        acc in
  Literal.Set.foldr addLit [] (largestLiterals cl)
;;

let addLit (lit,acc) =
  let addTm (path,tm) acc = (lit,path,tm) :: acc in
  List.foldl addTm acc (Literal.nonVarTypedSubterms lit)
;;

let largestSubterms cl = Literal.Set.foldl addLit [] (largestLiterals cl);;

let allSubterms cl = Literal.Set.foldl addLit [] (literals cl);;

(* ------------------------------------------------------------------------- *)
(* Subsumption.                                                              *)
(* ------------------------------------------------------------------------- *)

let subsumes (subs : clause Subsume.subsume) cl =
  Subsume.isStrictlySubsumed subs (literals cl);;

(* ------------------------------------------------------------------------- *)
(* Simplifying rules: these preserve the clause id.                          *)
(* ------------------------------------------------------------------------- *)

let freshVars clause =
  Clause {clause with thm = Rule.freshVars clause.Clause.thm};;

let simplify clause =
  match Rule.simplify clause.Clause.thm with
  | None -> None
  | Some thm -> Some (Clause {clause with thm = thm})
;;

let reduce units clause =
  Clause {clause with thm = Units.reduce units clause.Clause.thm};;

let rewrite rewr (Clause {parameters; id; thm}) =
  let simp th =
    let Parameters {ordering} = parameters in
    let cmp = Knuth_bendix_order.compare ordering in
    Rewrite.rewriteIdRule rewr cmp id th in
  let thm =
    match Rewrite.peek rewr id with
    | None -> simp thm
    | Some ((_,thm),_) -> if Rewrite.isReduced rewr then thm else simp thm in
  let result = Clause {parameters = parameters; id = id; thm = thm} in
  result;;

(* ------------------------------------------------------------------------- *)
(* Inference rules: these generate new clause ids.                           *)
(* ------------------------------------------------------------------------- *)

let factor cl =
  let Clause {parameters; thm} = cl in
  let lits = largestLiterals cl in
  let apply sub = newClause parameters (Thm.subst sub thm) in
  List.map apply (Rule.factor' lits)
;;

let resolve (cl1,lit1) (cl2,lit2) =
  let parameters = cl1.Clause.parameters
  and th1 = cl1.Clause.thm
  and th2 = cl2.Clause.thm in
  let sub = Literal.unify Substitute.empty lit1 (Literal.negate lit2) in
  let lit1 = Literal.subst sub lit1 in let lit2 = Literal.negate lit1 in
  let th1 = Thm.subst sub th1
  and th2 = Thm.subst sub th2 in
  let _ = isLargerLiteral parameters (Thm.clause th1) lit1 ||
          raise (Error "resolve: clause1: ordering constraints") in
  let _ = isLargerLiteral parameters (Thm.clause th2) lit2 ||
          raise (Error "resolve: clause2: ordering constraints") in
  let th = Thm.resolve lit1 th1 th2 in
  let cl = Clause {parameters = parameters; id = newId (); thm = th} in
  cl
;;

let paramodulate (cl1,lit1,ort1,tm1) (cl2,lit2,path2,tm2) =
  let parameters = cl1.Clause.parameters
  and th1 = cl1.Clause.thm
  and th2 = cl2.Clause.thm in
  let sub = Substitute.unify Substitute.empty tm1 tm2 in
  let lit1 = Literal.subst sub lit1
  and lit2 = Literal.subst sub lit2
  and th1 = Thm.subst sub th1
  and th2 = Thm.subst sub th2 in
  let _ = isLargerLiteral parameters (Thm.clause th1) lit1 ||
          raise (Error "Clause.paramodulate: with clause: ordering") in
  let _ = isLargerLiteral parameters (Thm.clause th2) lit2 ||
          raise (Error "Clause.paramodulate: into clause: ordering") in
  let eqn = (Literal.destEq lit1, th1) in
  let (l_r,_) as eqn =
    match ort1 with
    | Rewrite.Left_to_right -> eqn
    | Rewrite.Right_to_left -> Rule.symEqn eqn in
  let _ = isLargerTerm parameters l_r ||
          raise (Error "Clause.paramodulate: equation: ordering constraints") in
  let th = Rule.rewrRule eqn lit2 path2 th2 in
  Clause {parameters = parameters; id = newId (); thm = th}

end
;;

module Ax_cj = struct

type ax_cj_thm = Ax_cj_thm of {
  axioms_thm : Thm.thm list;
  conjecture_thm : Thm.thm list
};;

type ax_cj_cl  = Ax_cj_cl of {
  axioms_cl : Clause.clause list;
  conjecture_cl : Clause.clause list
};;

end
;;
