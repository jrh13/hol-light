module Metis_mapping = struct

(*
open Metis_prover
*)

let reset_consts,fol_of_const,hol_of_const =
  Meson.reset_consts,Meson.fol_of_const,Meson.hol_of_const
;;

let preterm_of_const = preterm_of_term o hol_of_const o int_of_string;;

let prefix s = "__" ^ s;;

let rec preterm_of_fol_term = function
  | Term.Var x -> Varp (prefix x, dpty)
  | Term.Fn (f, args) ->
      let pf = preterm_of_const f in
      let pargs = List.map preterm_of_fol_term args in
      Preterm.list_mk_combp (pf, pargs);;

let preterm_of_predicate = function
  | "=" -> Constp ("=", dpty)
  | p -> preterm_of_const p
;;

let preterm_of_atom (p, args) =
  let pp = preterm_of_predicate p in
  let pargs = List.map preterm_of_fol_term args in
  Typing (Preterm.list_mk_combp (pp, pargs), pretype_of_type bool_ty)
;;

let preterm_of_literal (pol, fat) =
  let pat = preterm_of_atom fat in
  if pol then pat else Preterm.mk_negp pat
;;

let preterm_of_eq (s, t) =
  Preterm.mk_eqp (preterm_of_fol_term s, preterm_of_fol_term t)
;;


let typecheck env =
  term_of_preterm o retypecheck env o Preterm.unconst_preterm;;
let typecheckl env = function
  | [] -> []
  | xs -> Preterm.list_mk_disjp xs |> typecheck env |> disjuncts
;;

let hol_of_term env = typecheck env o preterm_of_fol_term;;

let hol_of_atom env = typecheck env o preterm_of_atom;;

let hol_of_literal env = typecheck env o preterm_of_literal;;

let hol_of_clause env =
  typecheck env o Preterm.list_mk_disjp o map preterm_of_literal;;

let hol_of_substitution env = map dest_eq o typecheckl env o map preterm_of_eq;;

end (* struct Metis_mapping *)
