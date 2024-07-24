module Metis_unify = struct

let verb = ref false;;

exception Unify;;

let rec unify_fo_ho_term vars fat tm m =
  if !verb then
    begin
      print_string "unify_fo_ho_term: fat = ";
      print_string (Term.toString fat);
      print_string ", tm = ";
      print_string (string_of_term tm);
      print_newline ()
    end;
  match fat with
  | Term.Var_ v when List.exists (fun w, _ -> w = v) m ->
      if !verb then print_string "var_assoc\n";
      let tm' = assoc v m in
      if tm = tm' then m else raise Unify
  | Term.Var_ v ->
      if !verb then print_string "var\n";
      if is_var tm && not (mem tm vars) then (v, tm) :: m
      else (if !verb then print_string "Unify!\n"; raise Unify)
  | Term.Fn (f, args) ->
      if !verb then print_string "fn\n";
      let hf, hargs = try strip_comb tm with _ -> raise Unify in
      if !verb then begin
        print_string "hf = "; print_string (string_of_term hf);
        print_string "\n";
        print_string "is_var: ";
        print_string (if is_var hf then "true" else "false");
        print_string "\n"
      end;
      if not (is_const hf || is_var hf) then
        raise (Assert "is_const hf || is_var hf");
      if hf = Metis_mapping.hol_of_const (int_of_string f)
      then itlist2 (unify_fo_ho_term vars) args hargs m
      else raise Unify;;

let unify_fo_ho_atom vars (p, args) htm m =
  if p = "=" then
    try let hl, hr = dest_eq htm in
        itlist2 (unify_fo_ho_term vars) args [hl; hr] m
    with _ -> raise Unify
  else unify_fo_ho_term vars (Term.Fn (p, args)) htm m;;

let unify_fo_ho_literal vars (pol, atom) htm m =
  let htm' = if pol then htm else
             try dest_neg htm with _ -> raise Unify in
  unify_fo_ho_atom vars atom htm' m;;

end (* struct Metis_unify *)
;;
