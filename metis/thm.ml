(* ========================================================================= *)
(* A LOGICAL KERNEL FOR FIRST ORDER CLAUSAL THEOREMS                         *)
(* ========================================================================= *)

module Thm = struct

(* ------------------------------------------------------------------------- *)
(* An abstract type of first order logic theorems.                           *)
(* ------------------------------------------------------------------------- *)

type clause = Literal.literal Mset.set;;

type inferenceType =
    Axiom
  | Assume
  | Subst
  | Factor
  | Resolve
  | Refl
  | Equality;;

type thm = Thm of clause * (inferenceType * thm list);;

type inference = inferenceType * thm list;;

(* ------------------------------------------------------------------------- *)
(* Theorem destructors.                                                      *)
(* ------------------------------------------------------------------------- *)

let clause (Thm (cl,_)) = cl;;

let inference (Thm (_,inf)) = inf;;

(* Tautologies *)

let isTautology th =
  let chk = function
    | (_,None) -> None
    | ((pol,atm), Some set) ->
      if (pol && Atom.isRefl atm) || Atom.Set.member atm set then None
      else Some (Atom.Set.add set atm) in
  match Literal.Set.foldl chk (Some Atom.Set.empty) (clause th) with
  | Some _ -> false
  | None -> true;;

(* Contradictions *)

let isContradiction th = Literal.Set.null (clause th);;

(* Unit theorems *)

let destUnit (Thm (cl,_)) =
  if Literal.Set.size cl = 1 then Literal.Set.pick cl
  else raise (Error "Thm.destUnit");;

let isUnit = can destUnit;;

(* Unit equality theorems *)

let destUnitEq th = Literal.destEq (destUnit th);;

let isUnitEq = can destUnitEq;;

(* Literals *)

let member lit (Thm (cl,_)) = Literal.Set.member lit cl;;

let negateMember lit (Thm (cl,_)) = Literal.Set.negateMember lit cl;;

(* ------------------------------------------------------------------------- *)
(* A total order.                                                            *)
(* ------------------------------------------------------------------------- *)

let compare th1 th2 = Literal.Set.compare (clause th1) (clause th2);;

let equal th1 th2 = Literal.Set.equal (clause th1) (clause th2);;

(* ------------------------------------------------------------------------- *)
(* Free variables.                                                           *)
(* ------------------------------------------------------------------------- *)

let freeIn v (Thm (cl,_)) = Literal.Set.freeIn v cl;;

let freeVars (Thm (cl,_)) = Literal.Set.freeVars cl;;

(* ------------------------------------------------------------------------- *)
(* Pretty-printing.                                                          *)
(* ------------------------------------------------------------------------- *)

let inferenceTypeToString = function
  | Axiom -> "axiom"
  | Assume -> "assume"
  | Subst -> "subst"
  | Factor -> "factor"
  | Resolve -> "resolve"
  | Refl -> "refl"
  | Equality -> "equality"
;;

let toString (Thm (cl, (infType, ths))) =
  inferenceTypeToString infType ^ ": " ^ Literal.Set.toString cl

let rec print_proof (Thm (cl, (infType, ths))) =
  print_string ("Inference: " ^ inferenceTypeToString infType);
  print_break 0 0;
  print_string ("Clauses: " ^ Literal.Set.toString cl);
  print_break 0 0;
  print_string "Theorems: ";
  if ths = []
  then print_string "<none>"
  else begin
    print_break 0 0;
    open_vbox 2;
    print_break 0 0;
    List.app (print_proof) ths;
    close_box ()
  end;
  print_break 0 0
;;

(* ------------------------------------------------------------------------- *)
(* Primitive rules of inference.                                             *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----- axiom C                                                             *)
(*   C                                                                       *)
(* ------------------------------------------------------------------------- *)

let axiom cl = Thm (cl,(Axiom,[]));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ----------- assume L                                                      *)
(*   L \/ ~L                                                                 *)
(* ------------------------------------------------------------------------- *)

let assume lit =
  Thm (Literal.Set.fromList [lit; Literal.negate lit], (Assume,[]));;

(* ------------------------------------------------------------------------- *)
(*    C                                                                      *)
(* -------- subst s                                                          *)
(*   C[s]                                                                    *)
(* ------------------------------------------------------------------------- *)

let subst sub (Thm (cl,inf) as th) =
 let cl' = Literal.Set.subst sub cl in
 if Portable.pointerEqual (cl,cl') then th else
   match inf with
   | (Subst,_) -> Thm (cl',inf)
   | _ -> Thm (cl',(Subst,[th]))
;;

(* ------------------------------------------------------------------------- *)
(*   L \/ C    ~L \/ D                                                       *)
(* --------------------- resolve L                                           *)
(*        C \/ D                                                             *)
(*                                                                           *)
(* The literal L must occur in the first theorem, and the literal ~L must    *)
(* occur in the second theorem.                                              *)
(* ------------------------------------------------------------------------- *)

let resolve lit (Thm (cl1,_) as th1) (Thm (cl2,_) as th2) =
  let cl1' = Literal.Set.delete cl1 lit
  and cl2' = Literal.Set.delete cl2 (Literal.negate lit) in
  Thm (Literal.Set.union cl1' cl2', (Resolve,[th1;th2]))
;;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* --------- refl t                                                          *)
(*   t = t                                                                   *)
(* ------------------------------------------------------------------------- *)

let refl tm = Thm (Literal.Set.singleton (true, Atom.mkRefl tm), (Refl,[]));;

(* ------------------------------------------------------------------------- *)
(*                                                                           *)
(* ------------------------ equality L p t                                   *)
(*   ~(s = t) \/ ~L \/ L'                                                    *)
(*                                                                           *)
(* where s is the subterm of L at path p, and L' is L with the subterm at    *)
(* path p being replaced by t.                                               *)
(* ------------------------------------------------------------------------- *)

let equality lit path t =
  let s = Literal.subterm lit path in
  let lit' = Literal.replace lit (path,t) in
  let eqLit = Literal.mkNeq (s,t) in
  let cl = Literal.Set.fromList [eqLit; Literal.negate lit; lit'] in
  Thm (cl,(Equality,[]))
;;

end (* struct Thm *)
;;
