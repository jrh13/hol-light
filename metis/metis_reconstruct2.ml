module Metis_reconstruct2 = struct

let term_eq_mod_type t1 t2 tyinsts =
  try
    let _,tminsts,tyinsts = term_type_unify t1 t2 ([], [], tyinsts) in
    if !metisverb then
      begin
        print_string "unified with |tminsts| = ";
        print_string (Int.toString (List.length tminsts));
        print_string "!\n";
        List.app (fun (t1,t2) ->
          begin
            print_string (string_of_term t1);
            print_string " <- ";
            print_string (string_of_term t2);
            print_newline ()
          end) tminsts
      end;
    if not (List.null tminsts) then
      raise (Assert "tminsts = []");
    Some tyinsts
  with _ -> None
;;

let rec match_elems f m = function
  | ([], []) -> [m]
  | ([],  _) -> []
  | (x :: xs, ys) ->
      List.map (fun y ->
        match f x y m with
        | Some m' -> match_elems f m' (xs, List.filter (((<>) y)) ys)
        | None -> []) ys |> List.concat
;;

let match_fo_ho_clause vars =
  match_elems (fun ft ht m ->
    try Some (Metis_unify.unify_fo_ho_literal vars ft ht m)
    with Metis_unify.Unify -> None)
    []
;;

let string_of_tminst = String.concatWith ", " o
  map (fun (tm, v) -> string_of_term tm ^ " <- " ^ string_of_term v)
;;

let string_of_tyinst = String.concatWith ", " o
  map (fun (ty, v) -> string_of_type ty ^ " <- " ^ string_of_type v)
;;

let string_of_instantiation (it, tminst, tyinst) =
  "([" ^ string_of_tminst tminst ^ "], [" ^ string_of_tyinst tyinst ^ "])"
;;

let reorient_tysubst vars sub =
  let sub' = map (fun (ty, v) ->
    if mem v vars && is_vartype ty then v, ty else ty, v) sub in
  map (fun (ty, v) -> tysubst sub' ty, v) sub'
;;

let rec hol_of_thm axioms fth =
  if !metisverb then
    begin
      print_string "hol_of_thm: ";
      print_string (Thm.toString fth);
      print_string "\n"
    end;
  let env = Preterm.env_of_ths axioms in
  let hth =
    match Proof.thmToInference fth with
    | Proof.Axiom clause ->
        let clausel = Literal.Set.toList clause in
        let maxs = concat_map (fun ax ->
          let disjs = concl ax |> striplist dest_disj in
          let tmvars = freesl (hyp ax) in
          let ms = match_fo_ho_clause tmvars (clausel, disjs) in
          map (fun m -> m, ax) ms) axioms in
        if not (List.length maxs > 0) then
          raise (Assert "List.length maxs > 0");
        let tminst =
          List.map (fun (v, tm) ->
                      mk_var (Metis_mapping.prefix v, type_of tm), tm) in
        if !metisverb then
          begin
            print_string "length maxs = ";
            print_string (Int.toString (List.length maxs));
            print_string "\n"
          end;
        if !metisverb then
          List.app (fun (m, ax) ->
            begin
              print_string "max: ";
              print_string (string_of_thm ax);
              print_string " with m = ";
              print_string (string_of_tminst (tminst m));
              print_string "\n"
            end) maxs;
        let (m, ax) = List.hd maxs in
        INST (tminst m) ax
    (* Caution: the substitution can contain elements such as "x -> f(x)" *)
    | Proof.Subst (fsub, fth1) ->
        let th1 = hol_of_thm axioms fth1 in
        if !metisverb then
          begin
            print_string "subst with th1 = ";
            print_string (string_of_thm th1);
            print_string "\n"
          end;
        let fsubl = Substitute.toList fsub in
        if !metisverb then print_string "before substitution lifting\n";
        let hsub = map (fun (v, t) -> t, Term.Var_ v) fsubl |>
          Metis_mapping.hol_of_substitution env in
        if !metisverb then
          begin
            print_string "subst: ";
            print_string (string_of_tminst hsub);
            print_string "\n"
          end;
        let tyinst = itlist (fun (t, v) m ->
          let v' = find (fun v' -> name_of v' = name_of v) (frees (concl th1)) in
          type_unify (type_of v) (type_of v') m) hsub [] in
        let tminst = map (fun (t, v) -> inst tyinst t, inst tyinst v) hsub in
        if !metisverb then
          begin
            print_string "before instantiate of th1 = ";
            print_string (string_of_thm th1);
            print_string " with ";
            print_string (string_of_instantiation ([], tminst, tyinst));
            print_string "\n"
          end;
        INSTANTIATE ([], tminst, tyinst) th1
    | Proof.Resolve (atom, fth1, fth2) ->
        let th1 = hol_of_thm axioms fth1
        and th2 = hol_of_thm axioms fth2 in
        let env = Preterm.env_of_ths [th1; th2] @ env in
        if !metisverb then
          List.app (fun (s, pty) ->
            begin
              print_string s;
              print_string " <- ";
              print_string (string_of_type (type_of_pretype pty));
              print_string "\n"
            end) env;
        if !metisverb then print_string "before resolving\n";
        if !metisverb then
          begin
            print_string "th1 = ";
            print_string (string_of_thm th1);
            print_string "\n"
          end;
        if !metisverb then
          begin
            print_string "th2 = ";
            print_string (string_of_thm th2);
            print_string "\n"
          end;
        let tm1 = striplist dest_disj (concl th1) |> List.filter (not o is_neg)
        and tm2 = striplist dest_disj (concl th2)
                  |> List.filter is_neg |> List.map dest_neg in
        if !metisverb then
          List.app (fun s ->
            begin
              print_string "tm1: ";
              print_string (string_of_term s);
              print_string "\n"
            end) tm1;
        if !metisverb then
          List.app (fun s ->
            begin
              print_string "tm2: ";
              print_string (string_of_term s);
              print_string "\n"
            end) tm2;
        let hatom = Metis_mapping.hol_of_atom env atom in
        if !metisverb then
          begin
            print_string "hatom: ";
            print_string (string_of_term hatom);
            print_string "\n"
          end;
        let cands = List.concat (List.map (fun x ->
          match term_eq_mod_type hatom x [] with
            None -> []
          | Some m ->
              List.mapPartial (fun y -> term_eq_mod_type hatom y m) tm2) tm1) in
        if !metisverb then
          begin
            print_string (Int.toString (List.length cands));
            print_string " candidates available\n"
          end;
        if not (List.length cands > 0) then
          raise (Assert "List.length cands > 0");
        if not (let h = List.hd cands in List.all ((=) h) cands) then
          raise (Assert "(let h = List.hd cands in List.all ((=) h) cands)");
        let tyinsts = List.hd cands in
        let tyvars = map hyp axioms |> List.concat |>
          map type_vars_in_term |> List.concat in
        if !metisverb then print_string "Reorienting type substitution ...\n";
        let tyinsts = reorient_tysubst tyvars tyinsts in
        if !metisverb then print_string "Resolving ...\n";
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
        if !metisverb then
          begin
            print_string "Trying to replace ";
            print_string (string_of_term hs);
            print_string " : ";
            print_string (string_of_type (type_of hs));
            print_string " with ";
            print_string (string_of_term ht);
            print_string " : ";
            print_string (string_of_type (type_of ht));
            print_string "\nIn ";
            print_string (string_of_term hlit);
            print_string "\n"
          end;
        let heq = mk_eq (hs, ht) in
        let conv = PATH_CONV hpath (PURE_ONCE_REWRITE_CONV [ASSUME heq]) in
        let hlit' = CONV_RULE conv (ASSUME hlit) in
        if !metisverb then
          begin
            print_string "hlit = ";
            print_string (string_of_term hlit);
            print_string ", hlit' = ";
            print_string (string_of_thm hlit');
            print_string "\n"
          end;
        if hs <> ht then
          (if not (concl hlit' <> hlit) then
            raise (Assert "(concl hlit' <> hlit)")
          else ());
        (try Metis_rules.DISCH_DISJS [heq; hlit] hlit'
        with _ -> failwith "equality") in
  (* eliminate duplicates in clause *)
  let hth = CONV_RULE DISJ_CANON_CONV hth in
  if !metisverb then
    begin
      print_string "hol_of_thm finished\n";
      let hth' = Thm.clause fth |> Literal.Set.toList
                 |> Metis_mapping.hol_of_clause env in
      print_string "hol_of_thm returned:\n";
      print_string (string_of_term (concl hth));
      print_string " for\n";
      print_string (string_of_term hth');
      print_string "\n"
    end;
  hth
;;

end (* struct Metis_reconstruct2 *)
;;
