(* ========================================================================= *)
(* THE ACTIVE SET OF CLAUSES                                                 *)
(* ========================================================================= *)

module Active = struct

open Useful;;
open Order;;
open Ax_cj

(* ------------------------------------------------------------------------- *)
(* A type of active clause sets.                                             *)
(* ------------------------------------------------------------------------- *)

type simplify = Simplify of {
  subsumes : bool;
  reduce : bool;
  rewrites : bool
};;

type parameters = Parameters of {
  clause : Clause.parameters;
  prefactor : simplify;
  postfactor : simplify
};;

type active = Active of {
  parameters : parameters;
  clauses : Clause.clause Intmap.map;
  units : Units.units;
  rewrite : Rewrite.rewrite;
  subsume : Clause.clause Subsume.subsume;
  literals : (Clause.clause * Literal.literal) Literal_net.literalNet;
  equations :
      (Clause.clause * Literal.literal * Rewrite.orient * Term.term)
      Term_net.termNet;
  subterms :
      (Clause.clause * Literal.literal * Term.path * Term.term)
      Term_net.termNet;
  allSubterms : (Clause.clause * Term.term) Term_net.termNet
};;

let getSubsume (Active {subsume}) = subsume;;

let setRewrite active rewrite =
  {active with rewrite = rewrite};;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let maxSimplify = Simplify {
  subsumes = true;
  reduce = true;
  rewrites = true
};;

let default = Parameters {
  clause = Clause.default;
  prefactor = maxSimplify;
  postfactor = maxSimplify
};;

open Term_net
let empty parameters =
  let clause = parameters.clause in
  let ordering = clause.ordering in
  Active {
    parameters = parameters;
    clauses = Intmap.newMap ();
    units = Units.empty;
    rewrite = Rewrite.newRewrite (Knuth_bendix_order.compare ordering);
    subsume = Subsume.newSubsume ();
    literals = Literal_net.newNet false;
    equations = Term_net.newNet false;
    subterms = Term_net.newNet false;
    allSubterms = Term_net.newNet false
  };;

let size (Active {clauses}) = Intmap.size clauses;;

let clauses (Active {clauses}) =
  let add (_,cl,acc) = cl::acc in
  Intmap.foldr add [] clauses
;;

let saturation active =
  let remove (cl,(cls,subs)) =
    let lits = Clause.literals cl in
    if Subsume.isStrictlySubsumed subs lits then
      (cls,subs)
    else
      (cl::cls, Subsume.insert subs (lits, ())) in
  let cls = clauses active in
  let (cls,_) = List.foldl remove ([], Subsume.newSubsume ()) cls in
  let (cls,subs) = List.foldl remove ([], Subsume.newSubsume ()) cls in
  cls
 ;;

(* ------------------------------------------------------------------------- *)
(* Pretty printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let toString active = "Active{" ^ string_of_int (size active) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Simplify clauses.                                                         *)
(* ------------------------------------------------------------------------- *)

let simplify simp units rewr subs =
  let Simplify {subsumes; reduce; rewrites} = simp in
  let rewrite cl =
    let cl' = Clause.rewrite rewr cl in
    if Clause.equalThms cl cl' then
      Some cl
    else
      Clause.simplify cl' in
  fun cl ->
    match Clause.simplify cl with
    | None -> None
    | Some cl ->
        match (if rewrites then rewrite cl else Some cl) with
        | None -> None
        | Some cl ->
           let cl = if reduce then Clause.reduce units cl else cl in
           if subsumes && Clause.subsumes subs cl then None else Some cl
;;

let simplifyActive simp (Active {units; rewrite; subsume}) =
  simplify simp units rewrite subsume
;;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set.                                         *)
(* ------------------------------------------------------------------------- *)

let addUnit units cl =
  let th = Clause.thm cl in
  match total Thm.destUnit th with
  | Some lit -> Units.add units (lit,th)
  | None -> units
;;

let addRewrite rewrite cl =
  let th = Clause.thm cl in
  match total Thm.destUnitEq th with
  | Some l_r -> Rewrite.add rewrite (Clause.id cl, (l_r,th))
  | None -> rewrite
;;

let addSubsume subsume cl = Subsume.insert subsume (Clause.literals cl, cl);;

let addLiterals literals cl =
  let add ((_,atm) as lit, literals) =
    if Atom.isEq atm then
      literals
    else
      Literal_net.insert literals (lit,(cl,lit)) in
  Literal.Set.foldl add literals (Clause.largestLiterals cl)
;;

let addEquations equations cl =
  let add ((lit,ort,tm),equations) =
    Term_net.insert equations (tm,(cl,lit,ort,tm)) in
  List.foldl add equations (Clause.largestEquations cl)
;;

let addSubterms subterms cl =
  let add ((lit,path,tm),subterms) =
    Term_net.insert subterms (tm,(cl,lit,path,tm)) in
  List.foldl add subterms (Clause.largestSubterms cl)
;;

let addAllSubterms allSubterms cl =
  let add ((_,_,tm),allSubterms) = Term_net.insert allSubterms (tm,(cl,tm)) in
  List.foldl add allSubterms (Clause.allSubterms cl)
;;

let addClause active cl =
  let Active {clauses; subsume; literals; equations; subterms; allSubterms} =
    active in
  let clauses = Intmap.insert clauses (Clause.id cl, cl)
  and subsume = addSubsume subsume cl
  and literals = addLiterals literals cl
  and equations = addEquations equations cl
  and subterms = addSubterms subterms cl
  and allSubterms = addAllSubterms allSubterms cl in
  {active with clauses = clauses; subsume = subsume; literals = literals;
               equations = equations; subterms = subterms;
               allSubterms = allSubterms}
;;

let addFactorClause active cl =
  let Active {units; rewrite} = active in
  let units = addUnit units cl
  and rewrite = addRewrite rewrite cl in
  {active with units = units; rewrite = rewrite}
;;

(* ------------------------------------------------------------------------- *)
(* Derive (unfactored) consequences of a clause.                             *)
(* ------------------------------------------------------------------------- *)

let deduceResolution literals cl ((_,atm) as lit, acc) =
  let resolve (cl_lit,acc) =
    match total (Clause.resolve cl_lit) (cl,lit) with
    | Some cl' -> cl' :: acc
    | None -> acc in
  if Atom.isEq atm then
    acc
  else
    List.foldl resolve acc (Literal_net.unify literals (Literal.negate lit))
;;

let deduceParamodulationWith subterms cl ((lit,ort,tm),acc) =
  let para (cl_lit_path_tm,acc) =
    match total (Clause.paramodulate (cl,lit,ort,tm)) cl_lit_path_tm with
            Some cl' -> cl' :: acc
          | None -> acc in
  List.foldl para acc (Term_net.unify subterms tm)
;;

let deduceParamodulationInto equations cl ((lit,path,tm),acc) =
  let para (cl_lit_ort_tm,acc) =
    match total (Clause.paramodulate cl_lit_ort_tm) (cl,lit,path,tm) with
    | Some cl' -> cl' :: acc
    | None -> acc in
  List.foldl para acc (Term_net.unify equations tm)
;;

let deduce active cl =
  let Active {literals;equations;subterms} = active in
  let lits = Clause.largestLiterals cl in
  let eqns = Clause.largestEquations cl in
  let subtms =
    if Term_net.null equations then [] else Clause.largestSubterms cl in
  let acc = [] in
  let acc = Literal.Set.foldl (deduceResolution literals cl) acc lits in
  let acc = List.foldl (deduceParamodulationWith subterms cl) acc eqns in
  let acc = List.foldl (deduceParamodulationInto equations cl) acc subtms in
  let acc = List.rev acc in
  acc
;;

(* ------------------------------------------------------------------------- *)
(* Extract clauses from the active set that can be simplified.               *)
(* ------------------------------------------------------------------------- *)

let clause_rewritables active =
  let Active {clauses=clauses;rewrite=rewrite} = active in
  let rewr (id,cl,ids) =
    let cl' = Clause.rewrite rewrite cl in
    if Clause.equalThms cl cl' then ids else Intset.add ids id in
  Intmap.foldr rewr Intset.empty clauses
;;

let orderedRedexResidues (((l,r),_),ort) =
  match ort with
    None -> []
  | Some Rewrite.Left_to_right -> [(l,r,true)]
  | Some Rewrite.Right_to_left -> [(r,l,true)]
;;

let unorderedRedexResidues (((l,r),_),ort) =
  match ort with
    None -> [(l,r,false);(r,l,false)]
  | Some _ -> []
;;

let rewrite_rewritables active rewr_ids =
  let Active {parameters;rewrite;clauses;allSubterms} = active in
  let Parameters {clause} = parameters in
  let Clause {ordering} = clause in
  let order = Knuth_bendix_order.compare ordering in
  let addRewr (id,acc) =
    if Intmap.inDomain id clauses then Intset.add acc id else acc in
  let addReduce ((l,r,ord),acc) =
    let isValidRewr tm =
      match total (Substitute.matchTerms Substitute.empty l) tm with
      | None -> false
      | Some sub ->
          ord || let tm' = Substitute.subst (Substitute.normalize sub) r in
                 order (tm,tm') = Some Greater in
    let addRed ((cl,tm),acc) =
      let id = Clause.id cl in
        if Intset.member id acc then acc
        else if not (isValidRewr tm) then acc
        else Intset.add acc id in
    List.foldl addRed acc (Term_net.matched allSubterms l) in
  let addEquation redexResidues (id,acc) =
    match Rewrite.peek rewrite id with
    | None -> acc
    | Some eqn_ort -> Mlist.foldl addReduce acc (redexResidues eqn_ort) in
  let addOrdered = addEquation orderedRedexResidues in
  let addUnordered = addEquation unorderedRedexResidues in
  let ids = Intset.empty in
  let ids = Mlist.foldl addRewr ids rewr_ids in
  let ids = Mlist.foldl addOrdered ids rewr_ids in
  let ids = Mlist.foldl addUnordered ids rewr_ids in
  ids
;;

let choose_clause_rewritables active ids = size active <= length ids
  let rewritables active ids =
    if choose_clause_rewritables active ids then clause_rewritables active
    else rewrite_rewritables active ids
;;

let delete active ids =
  if Intset.null ids then active else
  let idPred id = not (Intset.member id ids) in
  let clausePred cl = idPred (Clause.id cl) in
  let Active {clauses; subsume; literals; equations; subterms; allSubterms} =
    active in
  let cP1 (x,_) = clausePred x in
  let cP1_4 (x,_,_,_) = clausePred x in
  let clauses = Intmap.filter (fun x -> idPred (fst x)) clauses
  and subsume = Subsume.filter clausePred subsume
  and literals = Literal_net.filter cP1 literals
  and equations = Term_net.filter cP1_4 equations
  and subterms = Term_net.filter cP1_4 subterms
  and allSubterms = Term_net.filter cP1 allSubterms in
  {active with clauses = clauses; subsume = subsume;
               literals = literals; equations = equations;
               subterms = subterms; allSubterms = allSubterms}
;;

let extract_rewritables (Active {clauses=clauses;rewrite=rewrite} as active) =
  if Rewrite.isReduced rewrite then (active,[]) else
  let (rewrite,ids) = Rewrite.reduce' rewrite in
  let active = setRewrite active rewrite in
  let ids = rewritables active ids in
  let cls = Intset.transform (Intmap.get clauses) ids in
  (delete active ids, cls)
;;

(* ------------------------------------------------------------------------- *)
(* Factor clauses.                                                           *)
(* ------------------------------------------------------------------------- *)

let prefactor_simplify active subsume =
  let Active {parameters; units; rewrite} = active in
  let Parameters {prefactor} = parameters in
  simplify prefactor units rewrite subsume
;;

let postfactor_simplify active subsume =
  let Active {parameters; units; rewrite} = active in
  let Parameters {postfactor} = parameters in
  simplify postfactor units rewrite subsume
;;

let sort_utilitywise =
  let utility cl =
    match Literal.Set.size (Clause.literals cl) with
    | 0 -> -1
    | 1 -> if Thm.isUnitEq (Clause.thm cl) then 0 else 1
    | n -> n in
  sortMap utility Int.compare
;;

let rec post_factor (cl, ((active,subsume,acc) as active_subsume_acc)) =
  match postfactor_simplify active subsume cl with
  | None -> active_subsume_acc
  | Some cl' ->
      if Clause.equalThms cl' cl then
        let active = addFactorClause active cl
        and subsume = addSubsume subsume cl
        and acc = cl::acc in
        (active,subsume,acc)
      else
        (* If the clause was changed in the post-factor simplification *)
        (* step, then it may have altered the set of largest literals *)
        (* in the clause. The safest thing to do is to factor again. *)
        factor1 (cl', active_subsume_acc)
and factor1 (cl, active_subsume_acc) =
  let cls = sort_utilitywise (cl::Clause.factor cl) in
  List.foldl post_factor active_subsume_acc cls
;;

let pre_factor (cl, ((active,subsume,_) as active_subsume_acc)) =
  match prefactor_simplify active subsume cl with
  | None -> active_subsume_acc
  | Some cl -> factor1 (cl, active_subsume_acc)
;;

let rec factor' active acc =
  function
  | [] -> (active, List.rev acc)
  | cls ->
      let cls = sort_utilitywise cls in
      let subsume = getSubsume active in
      let (active,_,acc) = Mlist.foldl pre_factor (active,subsume,acc) cls in
      let (active,cls) = extract_rewritables active in
      factor' active acc cls
;;

let factor active cls = factor' active [] cls;;

(* ------------------------------------------------------------------------- *)
(* Create a new active clause set and initialize clauses.                    *)
(* ------------------------------------------------------------------------- *)

let mk_clause params th =
  Clause.mk { Clause.parameters = params;
              Clause.id = Clause.newId ();
              Clause.thm = th
  };;

let newActive parameters {axioms_thm; conjecture_thm} =
  let {clause=clause} = parameters in
  let mk_clause = mk_clause clause in
  let active = empty parameters in
  let (active,axioms) = factor active (List.map mk_clause axioms_thm) in
  let (active,conjecture) = factor active (List.map mk_clause conjecture_thm) in
  (active, {axioms_cl = axioms; conjecture_cl = conjecture})
;;

(* ------------------------------------------------------------------------- *)
(* Add a clause into the active set and deduce all consequences.             *)
(* ------------------------------------------------------------------------- *)

let add active cl =
  match simplifyActive maxSimplify active cl with
  | None -> (active,[])
  | Some cl' ->
      if Clause.isContradiction cl' then
        (active,[cl'])
      else if not (Clause.equalThms cl cl') then
        factor active [cl']
      else
        let active = addClause active cl in
        let cl = Clause.freshVars cl in
        let cls = deduce active cl in
        let (active,cls) = factor active cls in
        (active,cls)
;;

end
