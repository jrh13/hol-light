(* ========================================================================= *)
(* Conversion of HOL to Metis FOL.                                           *)
(* ========================================================================= *)

module Metis_generate = struct

open Metis_prover

let metis_name = string_of_int

let rec metis_of_term env consts tm =
  if is_var tm && not (mem tm consts) then
    (Term.Var(metis_name (Meson.fol_of_var tm)))
  else (
    let f,args = strip_comb tm in
    if mem f env then failwith "metis_of_term: higher order" else
    let ff = Meson.fol_of_const f in
    Term.Fn (metis_name ff, map (metis_of_term env consts) args))

let metis_of_atom env consts tm =
  try let (l, r) = dest_eq tm in
      let l' = metis_of_term env consts l
      and r' = metis_of_term env consts r in
      Atom.mkEq (l', r')
  with Failure _ ->
      let f,args = strip_comb tm in
      if mem f env then failwith "metis_of_atom: higher order" else
      let ff = Meson.fol_of_const f in
      (metis_name ff, map (metis_of_term env consts) args)

let metis_of_literal env consts tm =
  let (pol, tm') = try (false, dest_neg tm)
     with Failure _ -> (true,           tm)
  in (pol, metis_of_atom env consts tm')

let metis_of_clause th =
  let lconsts = freesl (hyp th) in
  let tm = concl th in
  let hlits = disjuncts tm in
  let flits = map (metis_of_literal [] lconsts) hlits in
  let set = Literal.Set.fromList flits in
  Thm.axiom set

let metis_of_clauses = map metis_of_clause

end
