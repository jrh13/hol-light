(* ========================================================================= *)
(* THE WAITING SET OF CLAUSES                                                *)
(* ========================================================================= *)

(* NOTE This code has been modified to use integer weights, and Num.num
   instead of floats. *)

module Waiting = struct

(* ------------------------------------------------------------------------- *)
(* A type of waiting sets of clauses.                                        *)
(* ------------------------------------------------------------------------- *)

type weight = Num.num;;

type modelParameters = Model_parameters of {
  model : Model.parameters;
  initialPerturbations : int;
  maxChecks : int option;
  perturbations : int;
  weight : int
};;

type parameters = Parameters of {
  symbolsWeight : weight;
  variablesWeight : weight;
  literalsWeight : weight;
  modelsP : modelParameters list
};;

type distance = Num.num;;

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
    weight = 1
  }];;

let default : parameters =
  Parameters {
    symbolsWeight = num_1;
    literalsWeight = num_1;
    variablesWeight = num_1;
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
  let check (parm,model) z =
    let Model_parameters {maxChecks; weight} = parm in
    let (vT,vF) = Model.check Model.interpretClause maxChecks model fv cl in
    z */ ((num_1 +/ num_of_int vT // num_of_int (vT + vF)) **/
          num_of_int weight) in
  List.foldl check num_1 (zip parms models)
;;

let perturbModels parms models cls =
  let perturb (parm,model) =
    let Model_parameters {perturbations} = parm in
    perturbModel model cls perturbations in
  List.app perturb (zip parms models)
;;

(* ------------------------------------------------------------------------- *)
(* Clause weights.                                                           *)
(* ------------------------------------------------------------------------- *)

let clauseSymbols cl = num_of_int (Literal.Set.typedSymbols cl);;

let clauseVariables cl =
  num_of_int (Name.Set.size (Literal.Set.freeVars cl) + 1);;

let clauseLiterals cl = num_of_int (Literal.Set.size cl);;

let clausePriority cl =
  num_of_int cl.Clause.Clause.id //
  num_of_int 1_000_000_000_000;;

let clauseWeight parm mods dist mcl cl =
  let Parameters {symbolsWeight; variablesWeight; literalsWeight;
                  modelsP} = parm in
  let lits = Clause.literals cl in
  let symbolsW = clauseSymbols lits **/ symbolsWeight in
  let variablesW = clauseVariables lits **/ variablesWeight in
  let literalsW = clauseLiterals lits **/ literalsWeight in
  let modelsW = checkModels modelsP mods mcl in
  let weight = dist */ symbolsW */ variablesW */ literalsW */ modelsW in
  let weight = weight +/ clausePriority cl in
  weight
;;

(* ------------------------------------------------------------------------- *)
(* Adding new clauses.                                                       *)
(* ------------------------------------------------------------------------- *)

let rat_sqrt s =
  let rec sqrt n =
    if n < 1 then s // num_2 else
      let p = sqrt (n - 1) in
      (p +/ (s // p)) // num_2 in
  sqrt 5;;

let add' waiting dist mcls cls =
  let Waiting {parameters; clauses; models} = waiting in
  let Parameters {modelsP} = parameters in
  (* let dist = dist +. Math.ln (Real.fromInt (length cls)) in *)
  let dist = dist +/ rat_sqrt (num_of_int (length cls)) in
  let addCl (mcl,cl) acc =
    let weight = clauseWeight parameters models dist mcl cl in
    Heap.add acc (weight,(dist,cl)) in
  let clauses = List.foldl addCl clauses (zip mcls cls) in
  perturbModels modelsP models mcls;
  Waiting {parameters = parameters; clauses = clauses; models = models}
;;

let add waiting (dist,cls) =
  if List.null cls then
    waiting
  else
    let waiting = add' waiting dist (mkModelClauses cls) cls in
    waiting
;;

let cmp (w1,_) (w2,_) = Num.compare w1 w2;;

let empty parameters axioms conjecture =
  let Parameters {modelsP} = parameters in
  let clauses = Heap.newHeap cmp
  and models = List.map (initialModel axioms conjecture) modelsP in
  Waiting {parameters = parameters; clauses = clauses; models = models}
;;

let newWaiting parameters (Ax_cj.Ax_cj_cl {axioms_cl; conjecture_cl}) =
  let mAxioms = mkModelClauses axioms_cl
  and mConjecture = mkModelClauses conjecture_cl in
  let waiting = empty parameters mAxioms mConjecture in
  if List.null axioms_cl && List.null conjecture_cl then
    waiting
  else
    add' waiting num_0 (mAxioms @ mConjecture) (axioms_cl @ conjecture_cl)
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
