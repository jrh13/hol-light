module Metis_reconstruct2 = struct

(*
open Metis_prover
*)

let term_eq_mod_type t1 t2 tyinsts =
  try
    let _,tminsts,tyinsts = term_type_unify t1 t2 ([], [], tyinsts) in
    if !metisverb then
    begin
      Format.printf "unified with |tminsts| = %d!\n%!" (List.length tminsts);
      List.iter (fun t1, t2 -> Format.printf "%s <- %s\n%!" (string_of_term t1) (string_of_term t2)) tminsts
    end;
    assert (tminsts = []);
    Some tyinsts
  with _ -> None
;;

let rec match_elems f m = function
  | ([], []) -> [m]
  | ([],  _) -> []
  | (x :: xs, ys) ->
      List.map (fun y -> match f x y m with
                         | Some m' ->
                             match_elems f m' (xs, List.filter ((!=) y) ys)
                         | None -> []) ys
      |> List.concat
;;

let match_fo_ho_clause vars =
  match_elems (fun ft ht m ->
    try Some (Metis_unify.unify_fo_ho_literal vars ft ht m)
    with Metis_unify.Unify -> None)
    []
;;

let string_of_tminst = String.concat ", " o
  map (fun (tm, v) -> string_of_term tm ^ " <- " ^ string_of_term v)
;;

let string_of_tyinst = String.concat ", " o
  map (fun (ty, v) -> string_of_type ty ^ " <- " ^ string_of_type v)
;;

let string_of_instantiation (it, tminst, tyinst) =
  "([" ^ string_of_tminst tminst ^ "], [" ^ string_of_tyinst tyinst ^ "])"
;;

let reorient_tysubst vars sub =
  let sub' = map (fun (ty, v) ->
    if List.mem v vars && is_vartype ty then v, ty else ty, v) sub in
  map (fun (ty, v) -> tysubst sub' ty, v) sub'
;;

let rec hol_of_thm axioms fth =
  if !metisverb then Format.printf "hol_of_thm: %s\n%!" (Thm.toString fth);
  let env = Preterm.env_of_ths axioms in
  let hth = match Proof.thmToInference fth with
    Proof.Axiom clause ->
      let clausel = Literal.Set.toList clause in
      let maxs = Utils.List.concat_map (fun ax ->
        (*if !metisverb then Format.printf "ax: %s\n%!" (string_of_thm ax);*)
        let disjs = concl ax |> striplist dest_disj in
        (*if !metisverb then Format.printf "before matching\n%!";*)
        let tmvars = freesl (hyp ax) in
        let ms = match_fo_ho_clause tmvars (clausel, disjs) in
        (*if !metisverb then Format.printf "after matching\n%!";*)
        map (fun m -> m, ax) ms) axioms in
      assert (List.length maxs > 0);
      let tminst =
        List.map (fun v, tm ->
                    mk_var (Metis_mapping.prefix v, type_of tm), tm) in
      if !metisverb then
        Format.printf "length maxs = %d\n%!" (List.length maxs);
      if !metisverb then
        List.iter (fun (m, ax) -> Format.printf "max: %s with m = %s\n%!"
                                                (string_of_thm ax)
                                                (string_of_tminst (tminst m)))
                                                maxs;
      let (m, ax) = List.hd maxs in
      INST (tminst m) ax
  (* Caution: the substitution can contain elements such as "x -> f(x)" *)
  | Proof.Subst (fsub, fth1) ->
      let th1 = hol_of_thm axioms fth1 in
      if !metisverb then Format.printf "subst with th1 = %s\n%!"
                                       (string_of_thm th1);
      let fsubl = Substitute.toList fsub in
      if !metisverb then Format.printf "before substitution lifting\n%!";
      let hsub = map (fun (v, t) -> t, Term.Var v) fsubl |>
        Metis_mapping.hol_of_substitution env in
      if !metisverb then Format.printf "subst: %s\n%!" (string_of_tminst hsub);
      let tyinst = itlist (fun (t, v) m ->
        let v' = find (fun v' -> name_of v' = name_of v) (frees (concl th1)) in
        type_unify (type_of v) (type_of v') m) hsub [] in
      let tminst = map (fun (t, v) -> inst tyinst t, inst tyinst v) hsub in
      if !metisverb then
        Format.printf "before instantiate of th1 = %s with %s\n%!"
          (string_of_thm th1) (string_of_instantiation ([], tminst, tyinst));
      INSTANTIATE ([], tminst, tyinst) th1
  | Proof.Resolve (atom, fth1, fth2) ->
      let th1 = hol_of_thm axioms fth1
      and th2 = hol_of_thm axioms fth2 in
      let env = Preterm.env_of_ths [th1; th2] @ env in
      if !metisverb then
        List.iter (fun (s, pty) ->
          Format.printf "%s <- %s\n%!" s
                        (string_of_type (type_of_pretype pty))) env;
      if !metisverb then Format.printf "before resolving\n%!";
      if !metisverb then Format.printf "th1 = %s\n%!" (string_of_thm th1);
      if !metisverb then Format.printf "th2 = %s\n%!" (string_of_thm th2);
      let tm1 = striplist dest_disj (concl th1) |> List.filter (not o is_neg)
      and tm2 = striplist dest_disj (concl th2)
                |> List.filter is_neg |> List.map dest_neg in
      if !metisverb then
        List.iter (Format.printf "tm1: %s\n%!" o string_of_term) tm1;
      if !metisverb then
        List.iter (Format.printf "tm2: %s\n%!" o string_of_term) tm2;
      let hatom = Metis_mapping.hol_of_atom env atom in
      if !metisverb then Format.printf "hatom: %s\n%!" (string_of_term hatom);
      let cands = Utils.List.concat_map (fun x ->
        match term_eq_mod_type hatom x [] with
          None -> []
        | Some m ->
            Utils.List.filter_map (fun y -> term_eq_mod_type hatom y m) tm2)
                                  tm1 in
      if !metisverb then
        Format.printf "%d candidates available\n%!" (List.length cands);
      assert (List.length cands > 0);
      assert (let h = List.hd cands in List.for_all ((=) h) cands);
      let tyinsts = List.hd cands in
      let tyvars = map hyp axioms |> List.concat |>
        map type_vars_in_term |> List.concat in
      if !metisverb then Format.printf "Reorienting type substitution ...\n%!";
      let tyinsts = reorient_tysubst tyvars tyinsts in
      if !metisverb then Format.printf "Resolving ...\n%!";
      Metis_rules.RESOLVE (inst tyinsts hatom)
        (INST_TYPE tyinsts th1) (INST_TYPE tyinsts th2)
  | Proof.Refl term -> REFL (Metis_mapping.hol_of_term env term)
  | Proof.Assume atom ->
      SPEC (Metis_mapping.hol_of_atom env atom) EXCLUDED_MIDDLE
  | Proof.Equality (flit, fpath, ft) ->
      let hlit = Metis_mapping.hol_of_literal env flit in
      let fs, hpath = Metis_path.hol_of_literal_path flit fpath in
      let hs = follow_path hpath hlit in
      let ht = Metis_mapping.hol_of_term env ft in
      let m = type_unify (type_of ht) (type_of hs) [] in
      let hlit, hs, ht = inst m hlit, inst m hs, inst m ht in
      if !metisverb then begin
        Format.printf "Trying to replace %s : %s with %s : %s\n%!"
          (string_of_term hs) (string_of_type (type_of hs))
          (string_of_term ht) (string_of_type (type_of ht));
        Format.printf "In %s\n%!" (string_of_term hlit)
      end;
      let heq = mk_eq (hs, ht) in
      let conv = PATH_CONV hpath (PURE_ONCE_REWRITE_CONV [ASSUME heq]) in
      let hlit' = CONV_RULE conv (ASSUME hlit) in
      if !metisverb then Format.printf "hlit = %s, hlit' = %s\n%!"
        (string_of_term hlit) (string_of_thm hlit');
      if hs <> ht then assert (concl hlit' <> hlit);
      (try Metis_rules.DISCH_DISJS [heq; hlit] hlit'
      with _ -> failwith "equality")
  in
    (* eliminate duplicates in clause *)
    let hth = CONV_RULE DISJ_CANON_CONV hth in
    if !metisverb then begin
      Format.printf "hol_of_thm finished\n%!";
      let hth' = Thm.clause fth |> Literal.Set.toList |> Metis_mapping.hol_of_clause env in
      Format.printf "hol_of_thm returned:\n%s\n for\n%s\n%!"
        (string_of_term (concl hth)) (string_of_term hth')
    end;
    hth
end (* struct Metis_reconstruct2 *)
