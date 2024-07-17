(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* ========================================================================= *)

module Waiting = struct

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type weight = Real.real;;

type modelParameters = Model_parameters of {
  model : Model.parameters;
  initialPerturbations : int;
  maxChecks : int option;
  perturbations : int;
  weight : weight
};;

type parameters = Parameters of {
  symbolsWeight : weight;
  variablesWeight : weight;
  literalsWeight : weight;
  modelsP : modelParameters list
};;

type distance = Real.real;;

type waiting = Waiting of {
  parameters : parameters;
  clauses : (weight * (distance * Clause.clause)) Heap.heap;
  models : Model.model list
};;

(* ------------------------------------------------------------------------- *)
(* Basic operations.                                                         *)
(* ------------------------------------------------------------------------- *)

let defaultModels : modelParameters list = [
  Model_parameters {
    model = Model.default;
    initialPerturbations = 100;
    maxChecks = Some 20;
    perturbations = 0;
    weight = 1.0
  }];;

let default : parameters =
  Parameters {
    symbolsWeight = 1.0;
    literalsWeight = 1.0;
    variablesWeight = 1.0;
    modelsP = defaultModels
};;

let size (Waiting {clauses}) = Heap.size clauses;;

let toString w = "Waiting{" ^ Int.toString (size w) ^ "}";;

(* ------------------------------------------------------------------------- *)
(* Perturbing the models.                                                    *)
(* ------------------------------------------------------------------------- *)

type modelClause = Name.name Mset.set * Thm.clause;;

let mkModelClause cl =
  let lits = Clause.literals cl in
  let fvs = Literal.Set.freeVars lits in
  (fvs,lits)
;;

let mkModelClauses = List.map mkModelClause;;

let perturbModel vM cls =
  if List.null cls then
    kComb ()
  else
    let vN = Model.msize vM in
    let perturbClause (fv,cl) =
      let vV = Model.randomValuation vN fv in
      if not (Model.interpretClause vM vV cl) then ()
      else Model.perturbClause vM vV cl in
    let perturbClauses () = List.app perturbClause cls in
    fun n -> funpow n perturbClauses ()
;;

let initialModel axioms conjecture parm =
  let Model_parameters {model; initialPerturbations}  = parm in
  let m = Model.newModel model in
  let () = perturbModel m conjecture initialPerturbations in
  let () = perturbModel m axioms initialPerturbations in
  m
;;

let checkModels parms models (fv,cl) =
  let check ((parm,model),z) =
    let Model_parameters {maxChecks; weight} = parm in
    let n = maxChecks in
    let (vT,vF) = Model.check Model.interpretClause n model fv cl in
    Math.pow (1.0 +. Real.fromInt vT /. Real.fromInt (vT + vF), weight) *. z in
  List.foldl check 1.0 (zip parms models)
;;

let perturbModels parms models cls =
  let perturb (parm,model) =
    let {perturbations=perturbations} = parm in
    perturbModel model cls perturbations in
  app perturb (zip parms models)
;;

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

let clauseSymbols cl = Real.fromInt (Literal.Set.typedSymbols cl);;

let clauseVariables cl =
  Real.fromInt (Name.Set.size (Literal.Set.freeVars cl) + 1);;

let clauseLiterals cl = Real.fromInt (Literal.Set.size cl);;

let clausePriority cl = 1e-12 *. Real.fromInt (Clause.id cl);;

let clauseWeight parm mods dist mcl cl =
  let Parameters {symbolsWeight; variablesWeight; literalsWeight;
                  modelsP} = parm in
  let lits = Clause.literals cl in
  let symbolsW = Math.pow (clauseSymbols lits, symbolsWeight) in
  let variablesW = Math.pow (clauseVariables lits, variablesWeight) in
  let literalsW = Math.pow (clauseLiterals lits, literalsWeight) in
  let modelsW = checkModels modelsP mods mcl in
  let weight = dist *. symbolsW *. variablesW *. literalsW *. modelsW in
  let weight = weight +. clausePriority cl in
  weight
;;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

let add' waiting dist mcls cls =
  let Waiting {parameters; clauses; models} = waiting in
  let Parameters {modelsP} = parameters in
  let dist = dist +. Math.ln (Real.fromInt (length cls)) in
  let addCl ((mcl,cl),acc) =
    let weight = clauseWeight parameters models dist mcl cl in
    Heap.add acc (weight,(dist,cl)) in
  let clauses = List.foldl addCl clauses (zip mcls cls) in
  let () = perturbModels modelsP models mcls in
  Waiting {parameters; clauses; models}
;;

let add waiting (dist,cls) =
  if List.null cls then
    waiting
  else
    let waiting = add' waiting dist (mkModelClauses cls) cls in
    waiting
;;

let cmp (w1,_) (w2,_) = Real.compare w1 w2;;

let empty parameters axioms conjecture =
  let Parameters {modelsP} = parameters in
  let clauses = Heap.newHeap cmp
  and models = List.map (initialModel axioms conjecture) modelsP in
  Waiting {parameters; clauses; models}
;;

let newWaiting parameters (Ax_cj_cl {axioms_cl; conjecture_cl}) =
  let mAxioms = mkModelClauses axioms_cl
  and mConjecture = mkModelClauses conjecture_cl in
  let waiting = empty parameters mAxioms mConjecture in
  if List.null axioms_cl && List.null conjecture_cl then
    waiting
  else
    add' waiting 0.0 (mAxioms @ mConjecture) (axioms_cl @ conjecture_cl)
;;

(* ------------------------------------------------------------------------- *)
(* Removing the lightest clause.                                             *)
(* ------------------------------------------------------------------------- *)

let remove (Waiting {parameters; clauses; models}) =
  if Heap.null clauses then
    None
  else
    let ((_,dcl),clauses) = Heap.remove clauses in
    let waiting = Waiting {
                    parameters = parameters;
                    clauses = clauses;
                    models = models} in
    Some (dcl,waiting)
;;

end (* struct Waiting *)
;;
