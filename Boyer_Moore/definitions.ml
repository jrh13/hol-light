(******************************************************************************)
(* FILE          : definitions.ml                                             *)
(* DESCRIPTION   : Using definitions.                                         *)
(*                                                                            *)
(* READS FILES   : <none>                                                     *)
(* WRITES FILES  : <none>                                                     *)
(*                                                                            *)
(* AUTHOR        : R.J.Boulton                                                *)
(* DATE          : 6th June 1991                                              *)
(*                                                                            *)
(* LAST MODIFIED : R.J.Boulton                                                *)
(* DATE          : 3rd August 1992                                            *)
(*                                                                            *)
(* LAST MODIFIED : P. Papapanagiotou (University of Edinburgh)                *)
(* DATE          : 2008                                                       *)
(******************************************************************************)

(*----------------------------------------------------------------------------*)
(* recursive_calls : string -> term -> term list                              *)
(*                                                                            *)
(* Function to compute the occurrences of applications of a constant in a     *)
(* term. The first argument is the name of the constant. The second argument  *)
(* is the term to be examined. If there are no occurrences, an empty list is  *)
(* returned. The function assumes that the term does not contain              *)
(* abstractions.                                                              *)
(*----------------------------------------------------------------------------*)

let rec recursive_calls name tm =
 try (let (f,args) = strip_comb tm
  in  if (try(fst (dest_const f) = name) with Failure _ -> false)
      then [tm]
      else itlist List.append (map (recursive_calls name) args) [])
 with Failure _ -> [];;

(*----------------------------------------------------------------------------*)
(* is_subterm : term -> term -> bool                                          *)
(*                                                                            *)
(* Function to compute whether one term is a subterm of another.              *)
(*----------------------------------------------------------------------------*)

let rec is_subterm subterm tm =
try(   if (tm = subterm)
   then true
   else ((is_subterm subterm (rator tm)) || (is_subterm subterm (rand tm)))
  )with Failure _ -> false;;

(*----------------------------------------------------------------------------*)
(* no_new_terms : term -> term -> bool                                        *)
(*                                                                            *)
(* Function to determine whether all of the arguments of an application       *)
(* "f x1 ... xn" are subterms of a term.                                      *)
(*----------------------------------------------------------------------------*)

let no_new_terms app tm =
try
 (let args = snd (strip_comb app)
  in  itlist (fun x y -> x && y) (map (fun arg -> is_subterm arg tm) args) true
 ) with Failure _ -> failwith "no_new_terms";;

(*----------------------------------------------------------------------------*)
(* hide_fun_call : term -> term -> term                                       *)
(*                                                                            *)
(* Function to replace occurrences of a particular function call in a term    *)
(* with a genvar, so that `no_new_terms' can be used to look for arguments in *)
(* a term less the original call.                                             *)
(*----------------------------------------------------------------------------*)

let hide_fun_call app tm =
   let var = genvar (type_of app)
   in  subst [(var,app)] tm;;

(*----------------------------------------------------------------------------*)
(* is_explicit_value : term -> bool                                           *)
(*                                                                            *)
(* Function to compute whether a term is an explicit value. An explicit value *)
(* is either T or F or an application of a shell constructor to explicit      *)
(* values. A `bottom object' corresponds to an application to no arguments.   *)
(* I have also made numeric constants explicit values, since they are         *)
(* equivalent to some number of applications of SUC to 0.                     *)
(*----------------------------------------------------------------------------*)

let is_explicit_value tm =
   let rec is_explicit_value' constructors tm =
      (is_T tm) || (is_F tm) || ((is_const tm) && (type_of tm = `:num`)) ||
      (let (f,args) = strip_comb tm
       in  (try(mem (fst (dest_const f)) constructors) with Failure _ -> false) &
           (forall (is_explicit_value' constructors) args))
   in  is_explicit_value' (all_constructors ()) tm;;

(*----------------------------------------------------------------------------*)
(* more_explicit_values : term -> term -> bool                                *)
(*                                                                            *)
(* Returns true if and only if a new function call (second argument) has more *)
(* arguments that are explicit values than the old function call (first       *)
(* argument).                                                                 *)
(*----------------------------------------------------------------------------*)

let more_explicit_values old_call new_call =
try
 (let (f1,args1) = strip_comb old_call
  and (f2,args2) = strip_comb new_call
  in  if (f1 = f2)
      then let n1 = length (filter is_explicit_value args1)
           and n2 = length (filter is_explicit_value args2)
           in  n2 > n1
      else failwith "" ) with Failure _ -> failwith "more_explicit_values";;

(*----------------------------------------------------------------------------*)
(* good_properties : term list -> term -> term -> term -> bool                *)
(*                                                                            *)
(* Function to determine whether the recursive calls in the expansion of a    *)
(* function call have good properties. The first argument is a list of        *)
(* assumptions currently being made. The second argument is the original      *)
(* call. The third argument is the (simplified) expansion of the call, and    *)
(* the fourth argument is the term currently being processed and which        *)
(* contains the function call.                                                *)
(*----------------------------------------------------------------------------*)

(*< Boyer and Moore's heuristic
let good_properties assumps call body_of_call tm =
 let rec in_assumps tm assumps =
    if (assumps = [])
    then false
    else if (is_subterm tm (hd assumps))
         then true
         else in_assumps tm (tl assumps)
 in
 (let name = fst (dest_const (fst (strip_comb call)))
  and body_less_call = hide_fun_call call tm
  in  let rec_calls = recursive_calls name body_of_call
  in  let bools = map (fun rc -> (no_new_terms rc body_less_call) ||
                            (in_assumps rc assumps) ||
                            (more_explicit_values call rc)) rec_calls
  in  itlist (fun x y -> x && y) bools true
 ) with Failure _ -> failwith "good_properties";;
>*)

(* For HOL implementation, the restricted form of definitions allows all      *)
(* recursive calls to be considered to have good properties.                  *)

let good_properties assumps call body_of_call tm = true;;
