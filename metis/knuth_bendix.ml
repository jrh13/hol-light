(* ========================================================================= *)
(* KNUTH-BENDIX TERM ORDERING CONSTRAINTS                                    *)
(* ========================================================================= *)

module Knuth_bendix_order = struct

open Useful;;
open Order;;

(* ------------------------------------------------------------------------- *)
(* Helper functions.                                                         *)
(* ------------------------------------------------------------------------- *)

let notEqualTerm (x,y) = not (Term.equal x y);;

let firstNotEqualTerm f l =
    match Mlist.find notEqualTerm l with
      Some (x,y) -> f x y
    | None -> raise (Bug "firstNotEqualTerm");;

(* ------------------------------------------------------------------------- *)
(* The weight of all constants must be at least 1, and there must be at most *)
(* one unary function with weight 0.                                         *)
(* ------------------------------------------------------------------------- *)

type kbo =
     {weight : Term.function_t -> int;
      precedence : Term.function_t * Term.function_t -> order};;

(* Default weight = uniform *)

let uniformWeight : Term.function_t -> int = kComb 1;;

(* Default precedence = by arity *)

let arityPrecedence : Term.function_t * Term.function_t -> order =
    fun ((f1,n1),(f2,n2)) ->
       match Int.compare (n1,n2) with
         Less -> Less
       | Equal -> Name.compare (f1,f2)
       | Greater -> Greater;;

(* The default order *)

let default = {weight = uniformWeight; precedence = arityPrecedence};;

(* ------------------------------------------------------------------------- *)
(* Term weight-1 represented as a linear function of the weight-1 of the     *)
(* variables in the term (plus a constant).                                  *)
(*                                                                           *)
(* Note that the conditions on weight functions ensure that all weights are  *)
(* at least 1, so all weight-1s are at least 0.                              *)
(* ------------------------------------------------------------------------- *)

type weight = Weight of int Name.Map.map * int;;

let weightEmpty : int Name.Map.map = Name.Map.newMap ();;

let weightZero = Weight (weightEmpty,0);;

let weightIsZero (Weight (m,c)) = c = 0 && Name.Map.null m;;

let weightNeg (Weight (m,c)) = Weight (Name.Map.transform (fun x -> -x) m, -c);;

  let add ((_,n1),(_,n2)) =
        let n = n1 + n2
      in
        if n = 0 then None else Some n
      ;;
  let weightAdd (Weight (m1,c1)) (Weight (m2,c2)) =
      Weight (Name.Map.union add m1 m2, c1 + c2);;

let weightSubtract w1 w2 = weightAdd w1 (weightNeg w2);;

let weightTerm weight =
      let rec wt m c = function
          [] -> Weight (m,c)
        | (Term.Var v :: tms) ->
            let n = Option.getOpt (Name.Map.peek m v, 0)
          in
            wt (Name.Map.insert m (v, n + 1)) (c + 1) tms
        | (Term.Fn (f,a) :: tms) ->
          wt m (c + weight (f, length a)) (a @ tms)
    in
      fun tm -> wt weightEmpty (-1) [tm]
    ;;

let weightLowerBound (Weight (m,c)) =
    if Name.Map.exists (fun (_,n) -> n < 0) m then None else Some c;;

(* ------------------------------------------------------------------------- *)
(* The Knuth-Bendix term order.                                              *)
(* ------------------------------------------------------------------------- *)

let compare {weight=weight;precedence=precedence} =
      let weightDifference tm1 tm2 =
            let w1 = weightTerm weight tm1
            and w2 = weightTerm weight tm2
          in
            weightSubtract w2 w1

      in let rec weightLess tm1 tm2 =
            let w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceLess tm1 tm2
            else weightDiffLess w tm1 tm2

      and weightDiffLess w tm1 tm2 =
          match weightLowerBound w with
            None -> false
          | Some 0 -> precedenceLess tm1 tm2
          | Some n -> n > 0

      and precedenceLess x y = match (x,y) with
          (Term.Fn (f1,a1), Term.Fn (f2,a2)) ->
          (match precedence ((f1, length a1), (f2, length a2)) with
             Less -> true
           | Equal -> firstNotEqualTerm weightLess (zip a1 a2)
           | Greater -> false)
        | _ -> false

      in let weightDiffGreater w tm1 tm2 = weightDiffLess (weightNeg w) tm2 tm1

      in let rec weightCmp tm1 tm2 =
            let w = weightDifference tm1 tm2
          in
            if weightIsZero w then precedenceCmp tm1 tm2
            else if weightDiffLess w tm1 tm2 then Some Less
            else if weightDiffGreater w tm1 tm2 then Some Greater
            else None

      and precedenceCmp x y = match (x,y) with
          (Term.Fn (f1,a1), Term.Fn (f2,a2)) ->
          (match precedence ((f1, length a1), (f2, length a2)) with
             Less -> Some Less
           | Equal -> firstNotEqualTerm weightCmp (zip a1 a2)
           | Greater -> Some Greater)
        | _ -> raise (Bug "kboOrder.precendenceCmp")
    in
      fun (tm1,tm2) ->
         if Term.equal tm1 tm2 then Some Equal else weightCmp tm1 tm2
    ;;

end
