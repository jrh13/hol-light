module Metis_unify = struct

(*
open Metis_prover
*)

let verb = ref false

exception Unify

let rec unify_fo_ho_term vars fat tm m =
  if !verb then Format.printf "unify_fo_ho_term: fat = %s, tm = %s\n%!"
    (Term.toString fat) (string_of_term tm);
  match fat with
  | Term.Var v when List.mem_assoc v m ->
      if !verb then Format.printf "var_assoc\n%!";
      let tm' = List.assoc v m in
      if tm = tm' then m else raise Unify
  | Term.Var v ->
      if !verb then Format.printf "var\n%!";
      if is_var tm && not (List.mem tm vars) then (v, tm) :: m
      else (if !verb then Format.printf "Unify!\n%!"; raise Unify)
  | Term.Fn (f, args) ->
      if !verb then Format.printf "fn\n%!";
      let hf, hargs = try strip_comb tm with _ -> raise Unify in
      if !verb then begin
        Format.printf "hf = %s\n%!" (string_of_term hf);
        Format.printf "is_var: %s\n%!" (if is_var hf then "true" else "false")
      end;
      assert (is_const hf || is_var hf);
      if hf = Metis_mapping.hol_of_const (int_of_string f)
      then itlist2 (unify_fo_ho_term vars) args hargs m
      else raise Unify

let unify_fo_ho_atom vars (p, args) htm m =
  if p = "=" then
    try let hl, hr = dest_eq htm in
        itlist2 (unify_fo_ho_term vars) args [hl; hr] m
    with _ -> raise Unify
  else unify_fo_ho_term vars (Term.Fn (p, args)) htm m

let unify_fo_ho_literal vars (pol, atom) htm m =
  let htm' = if pol then htm else
             try dest_neg htm with _ -> raise Unify in
  unify_fo_ho_atom vars atom htm' m

end (* struct Metis_unify *)
