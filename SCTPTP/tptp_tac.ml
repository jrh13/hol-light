
#load "SCTPTP/tptpast.cmo";;
#load "SCTPTP/tptphelpers.cmo";;
#load "SCTPTP/tptpparser.cmo";;
#load "SCTPTP/tptplexer.cmo";;
#load "SCTPTP/tptplink.cmo";;

module Tptp_tac = struct 

  open Tptpast;;

  type tymap = (string * hol_type) list;;
  type defmap = (string * term) list;;

  let to_named_var (i: int) : string =
    Printf.sprintf "Var%d" i;;

  let to_named_fun (i: int) : string =
    Printf.sprintf "fun%d" i;;

  let idx_of_named_fun (s: string) : int =
    Scanf.sscanf s "fun%d" (fun x -> x);;

  let func_of_idx (i: int) : func = 
    Functor (to_named_fun i);;

  let name_of_functor (f: func) : string =
    match f with
    | Functor s -> s
    | Definedfunctor s -> s
    | Systemfunctor s -> s
    | Vfunctor s -> s;;

  let rec collect_assoc (xs: 'a list) (ys: ('a * 'b) list) : ('a * 'b) list =
    match xs with
    | [] -> []
    | x :: xs' -> 
        try let y = assoc x ys in 
          (x, y) :: collect_assoc xs' ys
        with _ -> collect_assoc xs' ys;; 

  let new_type_var = 
    let counter = ref 0 in
    fun () -> 
      let n = !counter in
      counter := n + 1;
      mk_vartype (Printf.sprintf "TPTPTy%d" n);;

  let reset_consts,idx_of_const,hol_of_idx =
    let false_tm = `F` in
    let cstore = ref ([]:(term * int)list)
    and ccounter = ref 2 in
    let reset_consts() = cstore := [false_tm,1]; ccounter := 2 in
    let _ = reset_consts () in
    let idx_of_const c =
      let currentconsts = !cstore in
      try assoc c currentconsts with Failure _ ->
      let n = !ccounter in
      ccounter := n + 1; cstore := (c,n)::currentconsts; n in
    let hol_of_idx c = rev_assoc c (!cstore) in
    reset_consts, idx_of_const, hol_of_idx;;

  let rec unify_types (ty_map: tymap) (ty1: hol_type) (ty2: hol_type) : hol_type * tymap =
    match ty1, ty2 with
    | Tyvar v, _ -> ty2, update_ty_map ((v, ty2) :: ty_map)
    | _, Tyvar v -> ty1, update_ty_map ((v, ty1) :: ty_map)
    | Tyapp (c1, tys1), Tyapp (c2, tys2) when c1 = c2 ->
      let tys, ty_map' = List.fold_right2 (fun t1 t2 (acc, tm) ->
        let t, tm' = unify_types tm t1 t2 in
          (t :: acc, tm')) tys1 tys2 ([], ty_map) in
        mk_type (c1, tys), ty_map'
    | _ -> failwith (Printf.sprintf "unify_types: incompatible types %s and %s" (string_of_type ty1) (string_of_type ty2))

  and update_ty_map (ty_map: tymap): tymap =
    let v, ty = hd ty_map in
    let vt = mk_vartype v in
    let sub = type_subst [vt, ty] in
      map (fun (vv, tt) -> (vv, sub tt)) ty_map;;

  (* Given a nested function type, construct a list of argument types and the output type *)
  let rec strip_fun_type_acc (ty : hol_type) (acc : hol_type list) : hol_type list * hol_type =
    match ty with
    | Tyapp (_, hd :: tl :: _) -> strip_fun_type_acc tl (hd :: acc)
    | _ -> (rev acc, ty)
  and strip_fun_type (ty : hol_type) : hol_type list * hol_type =
    strip_fun_type_acc ty [];;

  let rec hol_to_tptp (consts: term list) (h: term) : tptp_term = 
    (* check for quantifiers *)
    if is_forall h then
      let (x, t) = dest_forall h in
      let t' = hol_to_tptp consts t in
      let x' = hol_to_tptp consts x in
        Forall ([x'], t')
    else if is_exists h then
      let (x, t) = dest_exists h in
      let t' = hol_to_tptp consts t in
      let x' = hol_to_tptp consts x in
        Exist ([x'], t')
    else if is_eq h then (destruct_binary consts dest_eq (fun x y -> Equal (x, y)) h)
    else if is_conj h then (destruct_binary consts dest_conj (fun x y -> And (x, y)) h)
    else if is_disj h then (destruct_binary consts dest_disj (fun x y -> Or (x, y)) h)
    else if is_iff h then (destruct_binary consts dest_iff (fun x y -> Iff (x, y)) h)
    else if is_imp h then (destruct_binary consts dest_imp (fun x y -> Implies (x, y)) h)
    else if is_neg h then
      let t = dest_neg h in
      let t' = hol_to_tptp consts t in
        Not t'
    (* other special cases go here *)
    else
    inner_hol_to_tptp consts h
      
  and inner_hol_to_tptp (consts : term list) (h : term) : tptp_term =
    if (is_const h) || (mem h consts) then
      let idx = idx_of_const h in
      let cname = to_named_fun idx in
        Constant cname
    else if is_var h then (* && ! mem h consts*)
      let idx = idx_of_const h in (* we generate the index, but never expect to recover it for vars*)
      let vname = to_named_var idx in
        Var vname
    else
      let f, args = strip_comb h in
      let idx = idx_of_const f in
      let fn_f = func_of_idx idx in
      Functorapplication (fn_f, (args |> map (inner_hol_to_tptp consts)))

  and tptp_to_hol_typed (f: tptp_term) (ty_map: tymap) (def_map: defmap) (ty: hol_type) : term * (tymap) =
    match f with
    | Constant c ->
      let idx = idx_of_named_fun c in
      let hol_term = hol_of_idx idx in
      (* we know this term has a concrete type, so use it to constrain others if possible *)
      let _, ty_map' = unify_types ty_map ty (type_of hol_term) in
        hol_term, ty_map'
    | Var v ->
      (try let ty' = assoc v ty_map in
        (* we know a type for this, so unify *)
        let ty'', ty_map' = unify_types ty_map ty ty' in
          mk_var (v, ty''), (v, ty'') :: ty_map'
      with _ -> mk_var (v, ty), (v, ty) :: ty_map)
    | Fvar v ->
      (* we know that formula vars must be bool *)
      let _, ty_map' = unify_types ty_map ty bool_ty in
        mk_var (v, bool_ty), ty_map'
    | Functorapplication (f, args) ->
      (* we pretend that the functor is a term (of the right kind) *)
      (* and attempt to convert it via the standard mechanism *)
      let f_term = 
        match f with
        | Vfunctor v -> Var v
        | _ -> Constant (name_of_functor f) 
      in
      let var_fty = 
        List.fold_left (fun ty _ -> mk_fun_ty (new_type_var ()) ty) (new_type_var ()) args
      in
      let hf, ty_map' = tptp_to_hol_typed f_term ty_map def_map var_fty in
      let arg_types , res_type = strip_fun_type (type_of hf) in
      let _, ty_map'' = unify_types ty_map' res_type ty in
      let (hargs, ty_map''') =
        List.fold_right2 (fun a t (acc, tm) -> 
          let a', tm' = tptp_to_hol_typed a tm def_map t in
          (a' :: acc, tm')) args arg_types ([], ty_map'') in 
      let tt = list_mk_comb (hf, hargs) in
        propagate_unifiers tt ty_map''', ty_map'''
    | Definedconstant c ->
        (try let ff = assoc c def_map in
          let _, ty_map' = unify_types ty_map ty (type_of ff) in
            (propagate_unifiers ff ty_map'), ty_map'
        with _ -> failwith ("tptp_to_hol_typed: unknown defined constant " ^ c))
          
    (* Propositional operators *)

    | Not f -> 
      (* top-level type must be bool *)
      let _, ty_map' = unify_types ty_map ty bool_ty in
      (* inner term must be bool as well *)
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
      let tt = mk_neg hf in
        propagate_unifiers tt ty_map'', ty_map''

    | And (f, g) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
      let hg, ty_map''' = tptp_to_hol_typed g ty_map'' def_map bool_ty in
      let tt = mk_conj (hf, hg) in
        propagate_unifiers tt ty_map''', ty_map'''

    | Or (f, g) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
      let hg, ty_map''' = tptp_to_hol_typed g ty_map'' def_map bool_ty in
      let tt = mk_disj (hf, hg) in
        propagate_unifiers tt ty_map''', ty_map'''

    | Implies (f, g) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
      let hg, ty_map''' = tptp_to_hol_typed g ty_map'' def_map bool_ty in
      let tt = mk_imp (hf, hg) in
        propagate_unifiers tt ty_map''', ty_map'''

    | Iff (f, g) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
      let hg, ty_map''' = tptp_to_hol_typed g ty_map'' def_map bool_ty in
      let tt = mk_iff (hf, hg) in
        propagate_unifiers tt ty_map''', ty_map'''

    (* Quantifiers *)

    | Forall (vs, f) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in

      let vs', ty_map''' = 
        List.fold_right 
          (fun v (acc, tm) -> 
            let v', tm' = tptp_to_hol_untyped v tm def_map in 
              (v' :: acc, tm')
          ) 
          vs ([], ty_map'') in
      let cl_ty_map = List.filter (fun (x, _) -> not (List.mem (Var x) vs)) ty_map''' in
        list_mk_forall (vs', hf), cl_ty_map

    | Exist (vs, f) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
      let vs', ty_map''' = 
        List.fold_right 
          (fun v (acc, tm) -> 
            let v', tm' = tptp_to_hol_untyped v tm def_map in 
              (v' :: acc, tm')
          ) 
          vs ([], ty_map'') in
      let cl_ty_map = List.filter (fun (x, _) -> not (List.mem (Var x) vs)) ty_map''' in
        list_mk_exists (vs', hf), cl_ty_map

    | Epsilon (vs, f) ->
      if List.length vs != 1 then
        failwith (Printf.sprintf "epsilon term with incorrect number of arguments (%d)" (List.length vs))
      else 
        let v = List.hd vs in
        let hv, ty_map' = tptp_to_hol_typed v ty_map def_map ty in
        let hf, ty_map'' = tptp_to_hol_typed f ty_map' def_map bool_ty in
        let hv' = propagate_unifiers hv ty_map'' in
        let tt = mk_select (hv', hf) in
          tt, ty_map''

    | Equal (f, g) ->
      let _, ty_map' = unify_types ty_map ty bool_ty in
      let hf, ty_map'' = tptp_to_hol_untyped f ty_map' def_map in
      let fty = type_of hf in
      let hg, ty_map''' = tptp_to_hol_typed g ty_map'' def_map fty in
      let tt = mk_eq (propagate_unifiers hf ty_map''', hg) in
        tt, ty_map'''

    | _ -> failwith "tptp_to_hol_typed: unsupported term"

  and tptp_to_hol_untyped (f: tptp_term) (ty_map: tymap) (def_map: defmap) : term * (tymap) =
    match f with
    | Constant c ->
      let idx = idx_of_named_fun c in
      let hol_term = hol_of_idx idx in
      (* we know this term has a concrete type, so use it to constrain others if possible *)
      (* let the known procedure double-check this *)
      (* this is cheap, and should happen rarely *)
      tptp_to_hol_typed f ty_map def_map (type_of hol_term)
    | Var v ->
      (try let ty = assoc v ty_map in
        (* we have a known / assumed type for this, continue *)
        mk_var (v, ty), ty_map
      with _ ->
        (* make a fresh variable and let unification deal with it down the line *)
        let ty = (new_type_var ()) in
          tptp_to_hol_typed f ty_map def_map ty)
    | Fvar v ->
      (* we know that formula vars must be bool *)
      tptp_to_hol_typed f ty_map def_map bool_ty
    | Functorapplication _ ->
      (* make a fresh ty var, type_of func will concretize it *)
      (* if the function is a var as well, we don't have too much hope (locally) *)
      let ty = (new_type_var ()) in
        tptp_to_hol_typed f ty_map def_map ty
    | Definedconstant c ->
      (* rely on the definition having reasonable type info *)
      (* best effort *)
      tptp_to_hol_typed f ty_map def_map (new_type_var ())

    (* Propositional operators *)
    (* we know these must be concretely typed *)
    (* though we should not arrive here in the first place generally *)
    | Not _ -> 
      tptp_to_hol_typed f ty_map def_map bool_ty
    | And _ ->
      tptp_to_hol_typed f ty_map def_map bool_ty
    | Or _ ->
      tptp_to_hol_typed f ty_map def_map bool_ty
    | Implies _ ->
      tptp_to_hol_typed f ty_map def_map bool_ty
    | Iff _ ->
      tptp_to_hol_typed f ty_map def_map bool_ty

    (* Quantifiers *)
    | Forall _ ->
      tptp_to_hol_typed f ty_map def_map bool_ty
    | Exist _ ->
      tptp_to_hol_typed f ty_map def_map bool_ty
    | Epsilon (vs, f) ->
      (* weird, we reached an epsilon term without having type hints *)
      (* do our best, ig *)
      if List.length vs != 1 then
        failwith (Printf.sprintf "epsilon term with incorrect number of arguments (%d)" (List.length vs))
      else 
        let v = List.hd vs in
        (* unlike the typed case, do the body first *)
        let hf, ty_map' = tptp_to_hol_typed f ty_map def_map bool_ty in
        (* either this variable was found in f and assigned a type, 
          which could be a variable itself, or we just give it a 
          new one *)
        let hv, _ = tptp_to_hol_untyped v ty_map' def_map in
        let tt = mk_select (hv, hf) in
          tt, ty_map'
    
    | _ -> failwith "tptp_to_hol_untyped: unsupported term"

    (* update a term's type vars with accumulated unification info *)
  and propagate_unifiers (t: term) (ty_map: tymap) : term =
    let tyvars = type_vars_in_term t in
    let ty_subst = map (fun (x, y) -> (y, mk_vartype x)) (collect_assoc (map dest_vartype tyvars) ty_map) in
      inst ty_subst t

  and destruct_binary (consts: term list) (destructor: term -> (term * term)) (constructor: tptp_term -> tptp_term -> tptp_term) (h: term): tptp_term = 
    let (l, r) = destructor h in
    let l' = hol_to_tptp consts l in
    let r' = hol_to_tptp consts r in
      constructor l' r';;

  (* helper theorems *)

  let IMP_F_EQ = TAUT `((~b) ==> F) <=> b`;;
  let IMP_CONJ_EQ = TAUT `(a ==> (b ==> F)) <=> ((a /\ b) ==> F)`;;
  let NEG_IMP_DISJ_EQ = TAUT `((~a) ==> ((~b) ==> F)) <=> (~(a \/ b) ==> F)`;;
  let CONJ_IMP_EQ_IMP_CONJ = TAUT `((a ==> F) /\ (b ==> F)) <=> ((a \/ b) ==> F)`;;
  let IFF_CONJ_DEF = TAUT `((a ==> b) /\ (b ==> a)) <=> (a <=> b)`;;
  let IMP_NEG_DEF = TAUT `(b ==> F) <=> (~b)`;;
  let EQ_MP_CUT_RULE = UNDISCH_ALL (TAUT `a ==> ((a ==> b) ==> b)`);;

  (* helper steps *)

  let negate_abs (formula: term) : term =
    let v, body = dest_abs formula in
      mk_abs (v, (mk_neg body));;

  let imp_neg_elim (formula: term) (premise : thm) : thm =
    let inst_rule = INST [formula, `b: bool`] IMP_F_EQ in
      EQ_MP inst_rule premise;;

  let restore_right (formula: term) (premise: thm) : thm =
    imp_neg_elim formula (DISCH (mk_neg formula) premise);;

  let clear_right (formula: term) (premise: thm) : thm =
    let inst_rule = SYM (INST [formula, `b : bool`] IMP_F_EQ) in
      UNDISCH (EQ_MP inst_rule premise);;

  let typed_forall (ty: hol_type) : term =
    mk_const ("!", [ty, aty]);;

  let typed_exists (ty: hol_type) : term =
    mk_const ("?", [ty, aty]);;

  (* sctptp proof steps *)
  let left_false : thm =
    ASSUME `F`;;

  let right_true : thm =
    UNDISCH (TAUT `(~T) ==> F`);;

  let hypothesis (formula: term) : thm = 
    let base = ASSUME formula in
      clear_right formula base;;

  let weaken_left (formula: term) (premise: thm) : thm =
    UNDISCH (DISCH formula premise);;

  let weaken_right (formula: term) (premise: thm) : thm =
    let lform = mk_neg formula in
      weaken_left lform premise;;

  let weaken (left_formulas: term list) (right_formulas: term list) (premise: thm) : thm =
    let left_step = List.fold_left (fun p f -> weaken_left f p) premise left_formulas in
    let right_step = List.fold_left (fun p f -> weaken_right f p) left_step right_formulas in
      right_step ;;

  (*
    SC : Γ |- a, Δ  Σ, a |- Π
        ----------------------
            Γ, Σ |- Δ, Π

    ND:  Γ, ¬a, ¬Δ |- ⊥  Σ, a, ¬Π |- ⊥
        -------------------------------
              Γ, Σ, ¬Δ, ¬Π |- ⊥
  *)
  let cut (pivot: term) (left_prem: thm) (right_prem: thm) : thm =
    let clean_left_prem = restore_right pivot left_prem in
      PROVE_HYP clean_left_prem right_prem;;

  let left_and (a: term) (b: term) (premise: thm): thm =
    let imp_form_prem = DISCH a (DISCH b premise) in (* \Gamma |- a ==> b ==> F *)
    let inst_rule = INST [a, `a: bool`; b, `b: bool`] IMP_CONJ_EQ in 
    let right_proved = EQ_MP inst_rule imp_form_prem in (* \Gamma |- (a /\ b) ==> F *)
      UNDISCH right_proved;;

  let left_or (a: term) (b: term) (left_prem: thm) (right_prem: thm) : thm =
    let conj_prem = CONJ (DISCH a left_prem) (DISCH b right_prem) in
    let inst_rule = INST [a, `a: bool`; b, `b: bool`] CONJ_IMP_EQ_IMP_CONJ in
      UNDISCH (EQ_MP inst_rule conj_prem);;

  (**
    Note: no-op for ND here

    SC :   Γ |- a, Δ
        \-------------
          Γ, ¬ a |- Δ
        
    ND :  Γ, ¬ a, ¬ Δ |- ⊥
        \------------------
          Γ, ¬ a, ¬ Δ |- ⊥
  *)
  let left_not (_: term) (premise: thm) : thm =
    premise;;

  (*
    SC:   Γ |- a, Δ   Σ, b |- Π
        -------------------------
          Γ, Σ, a ==> b |- Δ, Π

    ND:   Γ, ¬a, ¬Δ |- ⊥   Σ, b, ¬Π |- ⊥
        ---------------------------------
          Γ, Σ, ¬Δ, ¬Π, a ==> b |- ⊥

  *)
  let left_imp (a: term) (b: term) (left_prem: thm) (right_prem: thm) : thm =
    let cut_rule = INST [a, `a: bool`; b, `b: bool`] EQ_MP_CUT_RULE in (* a, a ==> b |- b*)
    let clean_left = restore_right a left_prem in
      (* CUT 
          1 : |- a  
          2 : a, a ==> b |- b
          3 : b |- 
      *)
      PROVE_HYP (PROVE_HYP clean_left cut_rule) right_prem

  (*
    SC:   Γ, a[x := y] |- Δ
        ---------------------- y ∉ fv (Δ ∪ Γ)
            Γ, ∃x. a |- Δ

    ND:   Γ, ¬Δ, a[x := y] |- ⊥
        ------------------------- y ∉ fv (Δ ∪ Γ)
            Γ, ¬Δ, ∃x. a |- ⊥
  *)
  let left_ex (exa: term) (y: term) (premise: thm) : thm =
    let _, lambda_a = dest_comb exa in (* la *)
    let x, ax = dest_abs lambda_a in
    let ay = rand (concl (BETA_CONV (mk_comb (lambda_a, y)))) in (* a[x := y] *)
    let ytype = type_of y in
    let imp_prem = DISCH ay premise in (* |- a[x := y] ==> F *)
    let neg_def_rule = INST [ay, `b: bool`] IMP_NEG_DEF in
    let neg_a_prem = EQ_MP neg_def_rule imp_prem in (* |- ~a[x := y] *)
    let forall_a_prem =  GEN y neg_a_prem in (* |- ∀x. ~a*)
    let exists_forall_rule = SYM (SPEC lambda_a (INST_TYPE [ytype, `:A`] NOT_EXISTS_THM)) in (* |- ∀x. ~ ((la) x) <=> ~∃x. (la) x *)
    let forall_eta_conv = 
      let arg_conv =
        ABS y ( (* |- \y. ~ (la y) = \y. ~a[x := y] *)
          MK_COMB ( (* |- ~ (la y) = ~a[x := y] *)
            REFL `(~)`, (* |- (~) = (~) *)
            BETA_CONV (mk_comb (lambda_a, y)) (* |- la y = a[x := y] *)
        ))
      in
        SYM( (* |- !y. ~a[x := y] = !y. ~ (la y) *)
          MK_COMB ( (* |- !y. ~ (la y) = !y. ~a[x := y] *)
            REFL (typed_forall ytype), (* |- (!) = (!) *)
            arg_conv
        ))
    in
    let exists_eta_conv = 
      let ex_conv =
        MK_COMB ( (* |- ?y. (la y) = ?y. a[x := y] *)
          REFL (typed_exists ytype), (* |- (?) = (?) *)
          ABS y ( (* |- \y. (la y) = \y. a[x := y] *)
            BETA_CONV (mk_comb (lambda_a, y)) (* |- la y = a[x := y] *)
          )
        )
      in
        MK_COMB ( (* |- ~ ?y. (la y) = ~ ?y. a[x := y] *)
          REFL `(~)`, (* |- (~) = (~) *)
          ex_conv
        )
    in
    let exists_a_prem = EQ_MP exists_forall_rule (EQ_MP forall_eta_conv forall_a_prem) in 
    let exists_eta_reduced = EQ_MP exists_eta_conv exists_a_prem in
    let neg_def_exists_rule = SYM (INST [exa, `b: bool`] IMP_NEG_DEF) in (* turn into implication and undischarge *)
      UNDISCH (EQ_MP neg_def_exists_rule exists_eta_reduced);;


  (*
    SC:   Γ, a[x := t] |- Δ
        ----------------------
            Γ, ∀x. a |- Δ

    ND:   Γ, ¬Δ, a[x := t] |- ⊥
        -------------------------
            Γ, ¬Δ, ∀x. a |- ⊥
  *)
  let left_all (all_a: term) (t: term) (premise: thm) : thm =
    let _, lambda_a = dest_comb all_a in (* la *)
    let x, ax = dest_abs lambda_a in
    let at = rand (concl (BETA_CONV (mk_comb (lambda_a, t)))) in (* a[x := t] *)
    let ttype = type_of t in
    let imp_prem = DISCH at premise in (* |- a[x := t] ==> F *)
    let neg_def_rule = INST [at, `b: bool`] IMP_NEG_DEF in
    let neg_a_prem = EQ_MP neg_def_rule imp_prem in (* |- ~a[x := t] *)
    let exists_a_prem =  EXISTS (mk_exists (x, mk_neg ax), t) neg_a_prem in (* |- ∃x. ~a*) 
    let forall_exists_rule = SYM (SPEC lambda_a (INST_TYPE [ttype, `:A`] NOT_FORALL_THM)) in (* |- ∃x. ~ ((la) x) <=> ~∀x. (la) x *)
    let exists_eta_conv = 
      let arg_conv =
        ABS x ( (* |- \x. ~ (la x) = \x. ~a *)
          MK_COMB ( (* |- ~ (la x) = ~a *)
            REFL `(~)`, (* |- (~) = (~) *)
            BETA_CONV (mk_comb (lambda_a, x)) (* |- la x = a *)
        ))
      in
        SYM( (* |- ?x. ~a = ?x. ~ (la x) *)
          MK_COMB ( (* |- ?x. ~ (la x) = ?x. ~a *)
            REFL (typed_exists ttype), (* |- (?) = (?) *)
            arg_conv
        ))
    in
    let forall_eta_conv = 
      let all_conv =
        MK_COMB ( (* |- !x. (la x) = !x. a *)
          REFL (typed_forall ttype), (* |- (!) = (!) *)
          ABS x ( (* |- \x. (la x) = \x. a *)
            BETA_CONV (mk_comb (lambda_a, x)) (* |- la x = a *)
          )
        )
      in
        MK_COMB ( (* |- ~ !x. (la x) = ~ !x. a *)
          REFL `(~)`, (* |- (~) = (~) *)
          all_conv
        )
    in
    let forall_a_prem = EQ_MP forall_exists_rule (EQ_MP exists_eta_conv exists_a_prem) in 
    let forall_eta_reduced = EQ_MP forall_eta_conv forall_a_prem in
    let neg_def_exists_rule = SYM (INST [all_a, `b: bool`] IMP_NEG_DEF) in (* turn into implication and undischarge *)
      UNDISCH (EQ_MP neg_def_exists_rule forall_eta_reduced);;

  (*
    SC: Γ |- a, Δ   Σ |- b, Π
      -------------------------
        Γ, Σ |- a /\ b, Δ, Π

    ND: Γ, ¬a, ¬Δ |- ⊥   Σ, ¬b, ¬Π |- ⊥
      -----------------------------------
        Γ, Σ, ¬Δ, ¬Π, ¬ (a /\ b) |- ⊥
  *)
  let right_and (a: term) (b: term) (left_prem: thm) (right_prem: thm) : thm =
    let clean_left = restore_right a left_prem in
    let clean_right = restore_right b right_prem in
    let a_and_b = mk_conj (a, b) in
      clear_right a_and_b (CONJ clean_left clean_right)

  (*
    SC:    Γ |- a, Δ
      ------------------
        Γ |- a \/ b, Δ

    ND:    Γ, ¬a, ¬Δ |- ⊥
      ------------------------
        Γ, ¬Δ, ¬(a \/ b) |- ⊥
  *)
  let right_or (a: term) (b: term) (premise: thm) : thm =
    let right_proved = DISJ1 (restore_right a premise) b in
      clear_right (mk_disj (a, b)) right_proved;;

  let right_implies (a: term) (b: term) (premise: thm) : thm = 
    let rightb = restore_right b premise in
    let proved_imp = DISCH a rightb in
      clear_right (mk_imp (a, b)) proved_imp;;

  let right_iff (a: term) (b: term) (left_prem: thm) (right_prem: thm) : thm = 
    let a_b, b_a = mk_imp (a, b), mk_imp (b, a) in
    let aiffb = mk_iff (a, b) in
    (* create a => b /\ b => a on right *)
    let conj_imp = CONJ (restore_right a_b left_prem) (restore_right b_a right_prem) in
    let inst_rule = INST [a, `a: bool`; b, `b: bool`] IFF_CONJ_DEF in
    let proved_right = EQ_MP inst_rule conj_imp in
      clear_right aiffb proved_right;;
    
  let right_not (a: term) (premise: thm) : thm =
    let imp = DISCH a premise in
    let inst_rule = INST [a, `b: bool`] IMP_NEG_DEF in
      clear_right (mk_neg a) (EQ_MP inst_rule imp);;


  (**
    SC :   Γ |- a[x := t], Δ
        \--------------------
            Γ |- ∃x. a, Δ

    ND :    Γ, ¬ a[x := t], ¬ Δ |- ⊥
        \----------------------------
            Γ, ¬ ∃x. a, ¬ Δ |- ⊥
  *)
  let right_ex (ex_a: term) (t: term) (premise: thm) : thm =
    (* ex_a = ∃x. a *)
    let _, lambda_a = dest_comb ex_a in (* \lambda x. a *)
    let at = rand (concl (BETA_CONV (mk_comb (lambda_a, t)))) in (* a[x := t] *)
    let right_prem = restore_right at premise in
    let gen_prem = EXISTS (ex_a, t) right_prem in
      clear_right ex_a gen_prem;;

  (**
    SC :   Γ |- a[x := y], Δ
        \-------------------- x ∉ fv Γ
            Γ |- ∀x. a, Δ

    ND :    Γ, ¬ a[x := y], ¬ Δ |- ⊥
        \---------------------------- x ∉ fv Γ
              Γ, ¬ ∀x. a, ¬ Δ |- ⊥
  *)
  let right_all (all_a: term) (y: term) (premise: thm) : thm =
    (* all_a = ∀x. a *)
    let _, lambda_a = dest_comb all_a in (* \lambda x. a *)
    let ay = rand (concl (BETA_CONV (mk_comb (lambda_a, y)))) in (* a[x := y] *)
    let right_prem = restore_right ay premise in
    let gen_prem = GEN y right_prem in
      clear_right all_a gen_prem;;

  (** 
    SC : |- t = t

    ND : ~ t = t |- F 
  *)
  let right_refl (t: term) : thm = 
    clear_right (mk_eq (t, t)) (REFL t);;

  (**
    SC :     Γ, P(t) |- Δ
        \---------------------
          Γ, t = u, P(u) |- Δ

    ND :     Γ, P(t), ¬ Δ |- ⊥
        \-------------------------
          Γ, t = u, P(u), ¬Δ |- ⊥
  *)
  let left_subst (t: term) (u: term) (p: term) (premise: thm) : thm = 
    (* prove t = u, P(u) |- P(t) and cut *)
    let p_t, p_u = mk_comb (p, t), mk_comb (p, u) in (* P(t) and P(u) WITHOUT beta reduction *) 
    let beta_conv_t, beta_conv_u = BETA_CONV p_t, BETA_CONV p_u in (* |- P(t) = P_b(t) and for u *)
    let _, pt = dest_eq (concl beta_conv_t) in (* P_b(t) *)
    let _, pu = dest_eq (concl beta_conv_u) in (* P_b(u) *)
    let eq_rule = MK_COMB ((REFL p), (ASSUME (mk_eq (t,u)))) in (* t = u |- P(t) = P(u) (before beta red) *)
    let pu_beta = EQ_MP (SYM beta_conv_u) (ASSUME pu) in (* P_b(u) |- P(u) *)
    let pu_pt_beta = EQ_MP (SYM eq_rule) pu_beta in (* t = u, P_b(u) |- P(t) *)
    let pu_pt = EQ_MP beta_conv_t pu_pt_beta in (* t = u, P_b(u) |- P_b(t) *)
    let thm = PROVE_HYP pu_pt premise in
    thm
  ;;

  (**
    SC :     Γ |- P(t), Δ
        \---------------------
          Γ, t = u |- P(u), Δ

    ND :     Γ, ¬ P(t), ¬ Δ |- ⊥
        \---------------------------
          Γ, t = u, ¬ P(u), ¬Δ |- ⊥
  *)
  let right_subst (t: term) (u: term) (p: term) (premise: thm) : thm =
    left_subst t u (negate_abs p) premise;;

  let left_subst_iff = left_subst;;

  let right_subst_iff = right_subst;; 

  (*
    SC :   Γ[F := F] |- Δ[F := F]
        \---------------------------
          Γ[F := t] |- Δ[F := t]

    ND :   Γ[F := F], ¬Δ[F := F] |- ⊥
        \-----------------------------
          Γ[F := t], ¬Δ[F := t] |- ⊥

    CAVEAT: this step performs selective beta reduction after instantiation. If t
    already occurs as a beta redux in the premise, those instances will
    unfortunately be erroneously beta reduced as well.
  *)
  let inst_fun (f: term) (t: term) (premise: thm) : thm =
    let inst_base = INST [t, f] premise in
    let selective_beta =
      let conv tm =
        let lm, body = dest_comb tm in
        if aconv lm t then
          BETA_CONV tm
        else
          failwith "selective_beta: not the right term"
      in
      DEPTH_CONV conv 
    in
      CONV_RULE selective_beta inst_base;;

  let inst_pred = inst_fun;;

  (*
    Γ |- a[x := t]
    -----------------
    Γ |- a[x := εx.a]
  *)
  let prim_nd_epsilon (la: term) (t: term) (premise: thm) : thm =
    let epa = mk_select (dest_abs la) in (* epa = εx. a *)
    let bc_at = BETA_CONV (mk_comb (la, t)) in (* la t = a[x := t] *)
    let at = rand (concl bc_at) in (* a[x := t] *)
    let bc_epa = BETA_CONV (mk_comb (la, epa)) in (* la epa = a[x := epa] *)
    let aepa = rand (concl bc_epa) in (* a[x := epa] *)
    let ep_rule = UNDISCH (SPEC t (SPEC la (INST_TYPE [type_of t, aty] SELECT_AX))) in (* la t |- la epa *)
    let lat_prem = EQ_MP (SYM bc_at) premise in (* |- a[x := t] *)
    let epa_prem = PROVE_HYP lat_prem ep_rule in (* |- la epa *)
    let epa_eq = EQ_MP bc_epa epa_prem in (* |- a[x := epa] *)
      epa_eq;;

  (*
    SC :     Γ, a[x := y] |- Δ
        \------------------------
          Γ, a[x := εx.a] |- Δ

    ND :     Γ, a[x := y], ¬ Δ |- ⊥
        \----------------------------
          Γ, a[x := εx.a], ¬ Δ |- ⊥
  *)
  let left_epsilon (la: term) (y: term) (premise: thm) : thm =
    (* sadly this is not provable by prim_nd_epsilon :/ *)
    let exa = mk_exists (dest_abs la) in (* ∃x. a *)
    let ex_prem = left_ex exa y premise in (* ∃x. a |- *)
    let inst_ex_thm = INST_TYPE [type_of y, aty] EXISTS_THM in (* ∃ = (\P. P (@P)) *)
    let lp = rand (concl inst_ex_thm) in (* \P. P (@P) = lp *)
    let ex_eq = MK_COMB (INST_TYPE [type_of y, aty] EXISTS_THM, REFL la) in (* ∃ la = lp la *)
    let epa = mk_select (dest_abs la) in (* εx. a *)
    let pla_bc = 
      let epa_bc = BETA_CONV (mk_comb (la, epa)) in (* la epa = a[x := epa] *)
      let lp_bc = BETA_CONV (mk_comb (lp, la)) in (* lp la = la epa *)
      TRANS lp_bc epa_bc
    in (* lp la = a[x := epa] *)
    let ex_a_eq = TRANS ex_eq pla_bc in (* ∃ la = a[x := epa] *)
    let inv_ex_a_eq = (* ∃ la ==> F = a[x := epa] ==> F *)
      MK_COMB (MK_COMB (REFL `==>`, ex_a_eq), REFL `F`)
    in
      UNDISCH (EQ_MP inv_ex_a_eq (DISCH exa ex_prem)) ;;


  (*
    SC :     Γ |- a[x := t], Δ
        \------------------------
          Γ |- a[x := εx.a], Δ

    ND :     Γ, ¬a[x := y], ¬ Δ |- ⊥
        \------------------------------
          Γ, ¬a[x := εx.a], ¬ Δ |- ⊥
  *)
  let right_epsilon (la: term) (t: term) (premise: thm) : thm =
    let at = rand (concl (BETA_CONV (mk_comb (la, t)))) in (* a[x := t] *)
    let rprem = restore_right at premise in (* |- a[x := t] ==> F *)
    let post_ep = prim_nd_epsilon la t rprem in
      clear_right (concl post_ep) post_ep;;

  (* LEVEL 2 STEPS *)

  (* LEVEL 3 STEPS *)

  (* END STEPS ----------------------- *)

  let pretty_tptp (term: tptp_term) : string =
    let rec pretty_tptp' (term: tptp_term) : string =
      match term with
      | Constant c -> c
      | Var v -> v
      | Functorapplication (f, args) -> 
        let pretty_args = String.concat ", " (map pretty_tptp' args) in
        Printf.sprintf "%s(%s)" (name_of_functor f) pretty_args
      | Definedconstant c -> c
      | Not f -> Printf.sprintf "~(%s)" (pretty_tptp' f)
      | And (f, g) -> Printf.sprintf "(%s & %s)" (pretty_tptp' f) (pretty_tptp' g)
      | Or (f, g) -> Printf.sprintf "(%s | %s)" (pretty_tptp' f) (pretty_tptp' g)
      | Implies (f, g) -> Printf.sprintf "(%s => %s)" (pretty_tptp' f) (pretty_tptp' g)
      | Iff (f, g) -> Printf.sprintf "(%s <=> %s)" (pretty_tptp' f) (pretty_tptp' g)
      | Forall (vs, f) -> 
        let pretty_vs = String.concat ", " (map pretty_tptp' vs) in
        Printf.sprintf "(! [%s]: %s)" pretty_vs (pretty_tptp' f)
      | Exist (vs, f) -> 
        let pretty_vs = String.concat ", " (map pretty_tptp' vs) in
        Printf.sprintf "(? [%s]: %s)" pretty_vs (pretty_tptp' f)
      | Epsilon (vs, f) -> 
        let pretty_vs = String.concat ", " (map pretty_tptp' vs) in
        Printf.sprintf "(# [%s]: %s)" pretty_vs (pretty_tptp' f)
      | Equal (f, g) -> Printf.sprintf "(%s = %s)" (pretty_tptp' f) (pretty_tptp' g)
      | _ -> failwith "pretty_tptp: unsupported term"
    in
      pretty_tptp' term;;

  let pretty_sequent (s: sequent) : string =
    let Sequent (ant, suc) = s in
    if List.length ant = 0 && List.length suc = 1 then
      pretty_tptp (List.hd suc)
    else
      let pretty_ant = String.concat ", " (map pretty_tptp ant) in
      let pretty_suc = String.concat ", " (map pretty_tptp suc) in
        Printf.sprintf "[%s] --> [%s]" pretty_ant pretty_suc;;

  let pretty_fof (fof: annotated_formula) : string =
    let Fof {name = n; role = r; formula = f; annotations = a} = fof in
    let pretty_f = pretty_sequent f in
    (* let pretty_a = String.concat ", " (map (fun (k, v) -> Printf.sprintf "%s: %s" k v) a) in *)
      Printf.sprintf "fof(%s, %s, %s)." n r pretty_f;; (* TODO: print any annotations? *)

  let thm_to_tptp (consts: term list) (th: thm) : sequent =
    let ant, suc = dest_thm th in
    let ant' = map (hol_to_tptp consts) ant in
    let suc' = hol_to_tptp consts suc in
      Sequent (ant', [suc']);;

  type thm_map = (string * (thm * sequent)) list;;

  let emit_problem (axs: thm list) (ant: term list) (t: term) : (string * thm_map) =
    reset_consts ();
    let consts = List.append (List.flatten (List.map frees (t :: ant))) (List.flatten (List.map thm_frees axs)) in
    (* encode conjecture *)
    let fof_ants = List.map (hol_to_tptp consts) ant in
    let conjecture_term = hol_to_tptp consts t in
    let fof_conj = Fof {name = "problem"; role = "conjecture"; formula = Sequent(fof_ants, [conjecture_term]); annotations = None} in
    let conj_string = pretty_fof fof_conj in
    (* and axioms *)
    let ax_seqs = List.map (thm_to_tptp consts) axs in
    let ax_map = List.mapi (fun i (ax, ax_seq) -> (Printf.sprintf "ax%d" i, (ax, ax_seq))) (zip axs ax_seqs) in
    let fof_axs = List.map (function (i, (_, ax_seq)) -> Fof {name = i; role = "axiom"; formula = ax_seq; annotations = None}) ax_map in
    let ax_strings = List.map pretty_fof fof_axs in
    let ax_string = List.fold_left (fun acc s -> acc ^ s ^ "\n") "" ax_strings in
    let problem_string = ax_string ^ conj_string in
      (problem_string, ax_map)
    ;;

  let reconstruct_proof (axs: thm_map) (scps : annotated_formula list) : thm list =
    let def_map = ref ["$true", `T` ; "$false", `F`] in

    let reconstruct_proof' (acc : thm_map) (scp : annotated_formula) : thm_map =
      let Fof {name = n; role = role; formula = Sequent (ant, suc); annotations = a} = scp in
      if String.equal role "conjecture" then
        acc
      else if String.equal role "axiom" then
        let axref = assoc n axs in
          (n, axref) :: acc
      else if String.equal role "let" then
        if List.length ant != 0 then failwith "let formula should have no antecedents"
        else if List.length suc != 1 then failwith "let formula should have one conclusion"
        else 
          let binding :: _ = suc in
          (* store in def map *)
          let bind_name = "$" ^ n in
          let fbinding, _ = tptp_to_hol_untyped binding [] !def_map in
          let def_map' = (bind_name, fbinding) :: !def_map in
            def_map := def_map';
            acc
      else 
        (* should be a normal proof step *)
        (try 
          let source, _ = Option.get a in
          let Inference (rule, params, parents) = source in

          (* helpers / extractors *)

          let parent_thms = map (function (Parent (Named p, _)) -> (try assoc p acc with _ -> failwith ("Step " ^ n ^ " with unknown parent " ^ p) ) | _ -> failwith "unknown parent type") parents in

          let int_params = 
            List.filter_map (function Data (Num (Integer i), _) -> Some i | _ -> None) params
          in

          let term_params =
            List.filter_map (function Data (Fot t, _) -> Some t | _ -> None) params 
          in

          let string_params = 
            List.filter_map (function Data (String s, _) -> Some s | _ -> None) params
          in

          let seq_params = 
            List.filter_map (function Data (Fof seq, _) -> Some seq | _ -> None) params 
          in

          let list_params = 
            List.filter_map (function Listterm l -> Some l | _ -> None) params
          in

          let empty_map : tymap = [] in

          let formula_list_to_hol (ls: tptp_term list) (tm: tymap) =
            List.fold_left 
              (fun (acc, tm) f -> let f', tm' = tptp_to_hol_typed f tm !def_map bool_ty in f' :: acc, tm') 
              ([], tm) ls 
          in
          
          let formula_to_hol (f: tptp_term) (tm: tymap) = tptp_to_hol_typed f tm !def_map bool_ty in

          (* let matches_seq (th: thm) = 
            let expected_terms, _ = formula_list_to_hol (List.append ant (List.map (fun f -> Not f) suc)) empty_map in
            let found_terms = (concl th) :: (hyp th) in
            let ac = 
              List.for_all (fun f -> List.exists (aconv f) expected_terms) found_terms
            in
            let ac2 = 
              List.for_all (fun f -> List.exists (aconv f) found_terms) expected_terms
            in
            if (ac && ac2) then () else 
            let _ = (Printf.printf "THM MISMATCH!!! Wanted \n%s\nGOT\n%s" (String.concat ";; " (List.map string_of_term expected_terms)) (string_of_thm th))
            in
              (failwith "wrongthm")
          in *)

          let map_thm (th: thm) = 
            (* let _ = matches_seq th in *)
            (n, (th, Sequent (ant, suc))) :: acc in

          let remove (x: 'a) (xs: 'a list) : 'a list =
            List.filter (fun y -> y <> x) xs
          in

          let at_left (n: int) = List.nth ant n in

          let at_right (n: int) = List.nth suc n in

          (match rule with
          
          | "leftFalse" ->
            let pos_l :: _ = int_params in
            let ff = at_left pos_l in
            let wls = remove ff ant in
            let wrs = suc in
            let hwls, ty_map = formula_list_to_hol wls empty_map in
            let hwrs, ty_map' = formula_list_to_hol wrs ty_map in
            let hff, _ = formula_to_hol ff ty_map' in
            let thm = weaken hwls hwrs (left_false) in
              map_thm thm

          | "rightTrue" ->
            let pos_r :: _ = int_params in
            let tt = at_left pos_r in
            let wls = ant in
            let wrs = remove tt suc in
            let hwls, ty_map = formula_list_to_hol wls empty_map in
            let hwrs, ty_map' = formula_list_to_hol wrs ty_map in
            let hff, _ = formula_to_hol tt ty_map' in
            let thm = weaken hwls hwrs (right_true) in
              map_thm thm

          | "hyp" -> 
            let pos_l :: _ = int_params in
            let a = at_left pos_l in
            let wls = remove a ant in
            let wrs = remove a suc in
            let hwls, ty_map = formula_list_to_hol wls empty_map in
            let hwrs, ty_map' = formula_list_to_hol wrs ty_map in
            let ha, _ = formula_to_hol a ty_map' in
            let thm = weaken hwls hwrs (hypothesis ha) in
              map_thm thm

          | "leftWeaken" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let a = at_left pos_l in
            let ha, _ = formula_to_hol a empty_map in
            let thm = weaken_left ha p in
              map_thm thm

          | "rightWeaken" ->
            let pos_r :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let a = at_right pos_r in
            let ha, _ = formula_to_hol a empty_map in
            let thm = weaken_right ha p in
              map_thm thm

          | "cut" ->
            let pos_r :: _ = int_params in
            let (pl, pl_seq) :: (pr, _) :: _ = parent_thms in
            let Sequent (_, pl_succ) = pl_seq in
            let pivot = List.nth pl_succ pos_r in
            let hpivot, _ = formula_to_hol pivot empty_map in
            let thm = cut hpivot pl pr in
              map_thm thm

          | "leftAnd" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let a_and_b = at_left pos_l in
            let hab, _ = formula_to_hol a_and_b empty_map in
            let (ha, hb) = dest_conj hab in
            let thm = left_and ha hb p in
              map_thm thm

          | "leftOr" ->
            let pos_l :: _ = int_params in
            let (pl, _) :: (pr, _) :: _ = parent_thms in
            let a_or_b = at_left pos_l in
            let hab, _ = formula_to_hol a_or_b empty_map in
            let (ha, hb) = dest_disj hab in
            let thm = left_or ha hb pl pr in
              map_thm thm

          | "leftImplies" ->
            let pos_l :: _ = int_params in
            let (pl, _) :: (pr, _) :: _ = parent_thms in
            let a_imp_b = at_left pos_l in
            let hab, _ = formula_to_hol a_imp_b empty_map in
            let (ha, hb) = dest_imp hab in
            let thm = left_imp ha hb pl pr in
              map_thm thm

          | "leftNot" ->
            (* this is a no-op, but for uniformity, we let the implementing
            function handle that *)

            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let na = at_left pos_l in
            let hna, _ = formula_to_hol na empty_map in
            let ha = dest_neg hna in
            let thm = left_not ha p in
              map_thm thm

          | "leftExists" ->
            let pos_l :: _ = int_params in
            let y :: _ = string_params in
            let (p, _) :: _ = parent_thms in
            let ex_x_a = at_left pos_l in
            let hex_x_a, ty_map = formula_to_hol ex_x_a empty_map in
            let (x, _) = dest_exists hex_x_a in
            let xty = type_of x in
            (* y is just a variable, cannot be lifted in isolation *)
            (* either context or a concrete type must be given *)
            let hy, _ = tptp_to_hol_typed (Var y) ty_map !def_map xty in
            let thm = left_ex hex_x_a hy p in
              map_thm thm

          | "leftForall" ->

            let pos_l :: _ = int_params in
            let t :: _ = term_params in
            let (p, _) :: _ = parent_thms in
            let all_x_a = at_left pos_l in
            let hall_x_a, ty_map = formula_to_hol all_x_a empty_map in
            let (x, _) = dest_forall hall_x_a in
            let xty = type_of x in
            let ht, ty_map'' = tptp_to_hol_typed t ty_map !def_map xty in
            let thm = left_all (propagate_unifiers hall_x_a ty_map'') ht p in
              map_thm thm 

          | "rightAnd" ->
            let pos_r :: _ = int_params in
            let (pl, _) :: (pr, _) :: _ = parent_thms in
            let a_and_b = at_right pos_r in
            let hab, _ = formula_to_hol a_and_b empty_map in
            let (ha, hb) = dest_conj hab in
            let thm = right_and ha hb pl pr in
              map_thm thm

          | "rightOr" ->
            let pos_r :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let a_or_b = at_right pos_r in
            let hab, _ = formula_to_hol a_or_b empty_map in
            let (ha, hb) = dest_disj hab in
            let thm = right_or ha hb p in
              map_thm thm

          | "rightImplies" ->
            let pos_r :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let a_imp_b = at_right pos_r in
            let hab, _ = formula_to_hol a_imp_b empty_map in
            let (ha, hb) = dest_imp hab in
            let thm = right_implies ha hb p in
              map_thm thm

          | "rightIff" ->
            let pos_r :: _ = int_params in
            let (pl, _) :: (pr, _) :: _ = parent_thms in
            let a_iff_b = at_right pos_r in
            let hab, _ = formula_to_hol a_iff_b empty_map in
            let (ha, hb) = dest_iff hab in
            let thm = right_iff ha hb pl pr in
              map_thm thm

          | "rightNot" ->
            let pos_r :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let nega = at_right pos_r in
            let hnega, _ = formula_to_hol nega empty_map in
            let ha = dest_neg hnega in
            let thm = right_not ha p in
              map_thm thm

          | "rightExists" ->
            let pos_r :: _ = int_params in
            let t :: _ = term_params in
            let (p, _) :: _ = parent_thms in
            let ex_x_a = at_right pos_r in
            let hex_x_a, ty_map = formula_to_hol ex_x_a empty_map in
            let (x, ha) = dest_exists hex_x_a in
            let xty = type_of x in
            let ht, ty_map'' = tptp_to_hol_typed t ty_map !def_map xty in
            let thm = right_ex (propagate_unifiers hex_x_a ty_map'') ht p in
              map_thm thm

          | "rightForall" ->
            let pos_r :: _ = int_params in
            let y :: _ = string_params in
            let (p, _) :: _ = parent_thms in
            let all_x_a = at_right pos_r in
            let hall_x_a, ty_map = formula_to_hol all_x_a empty_map in
            let (x, ha) = dest_forall hall_x_a in
            let xty = type_of x in
            let hy, _ = tptp_to_hol_typed (Var y) ty_map !def_map xty in
            let thm = right_all ha hy p in
              map_thm thm

          | "rightRefl" ->
            let pos_r :: _ = int_params in
            let t_eq_t = at_right pos_r in
            let wls = ant in
            let wrs = remove t_eq_t suc in
            let hwls, ty_map = formula_list_to_hol wls empty_map in
            let hwrs, ty_map' = formula_list_to_hol wrs ty_map in
            let heq, _ = formula_to_hol t_eq_t ty_map' in
            let ht, _ = dest_eq heq in
            let thm = weaken hwls hwrs (right_refl ht) in
              map_thm thm

          | "leftSubst" | "leftSubstIff" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let (Sequent ([], [pz])) :: _ = seq_params in
            let flip_str :: z_name :: _ = string_params in 
            let t_eq_u = at_left pos_l in
            let hpz, ty_map = formula_to_hol pz empty_map in
            let heq, ty_map' = formula_to_hol t_eq_u ty_map in
            let (ht, hu) = dest_eq heq in
            let hz, _ = tptp_to_hol_typed (Var z_name) ty_map' !def_map (type_of ht) in
            let thm = 
              if flip_str = "true" then 
                let base_thm = left_subst hu ht (mk_abs (hz, (propagate_unifiers hpz ty_map'))) p in
                PROVE_HYP (SYM (ASSUME heq)) base_thm
              else
                let base_thm = left_subst ht hu (mk_abs (hz, (propagate_unifiers hpz ty_map'))) p in
                base_thm
            in
              map_thm thm

          | "rightSubst" | "rightSubstIff" ->
            let pos_l :: flip :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let (Sequent ([], [pz])) :: _ = seq_params in
            let z_name :: _ = string_params in 
            let t_eq_u = at_left pos_l in
            let hpz, ty_map = formula_to_hol pz empty_map in
            let heq, ty_map' = formula_to_hol t_eq_u ty_map in
            let (ht, hu) = dest_eq heq in
            let hz, _ = tptp_to_hol_typed (Var z_name) ty_map' !def_map (type_of ht) in
            let thm = 
              if flip = 1 then 
                let base_thm = right_subst hu ht (mk_abs (hz, (propagate_unifiers hpz ty_map'))) p in
                PROVE_HYP (SYM (ASSUME heq)) base_thm
              else
                let base_thm = right_subst ht hu (mk_abs (hz, (propagate_unifiers hpz ty_map'))) p in
                base_thm
            in
              map_thm thm

          | "instFun" | "instPred" ->
            let fname :: _ = string_params in
            let t :: _ = term_params in
            let (p, _) :: _ = parent_thms in
            let param_ls :: _ = list_params in
            let varnames = List.filter_map (function Data (String v, _) -> Some v | _ -> None) param_ls in
            let ty_map = List.fold_left (fun tm f -> snd (formula_to_hol f tm)) empty_map (List.rev_append ant suc) in
            let ht, _ = tptp_to_hol_untyped t ty_map !def_map in
            let hxs = List.map (fun x -> fst (tptp_to_hol_untyped (Var x) ty_map !def_map)) varnames in
            let lambda_t = List.fold_right (fun x t -> mk_abs (x, t)) hxs ht in
            let raw_type_f = try assoc fname ty_map with Not_found -> (new_type_var ()) in
            let fty, ty_map' = unify_types ty_map raw_type_f (type_of lambda_t) in
            let lambda_t' = propagate_unifiers lambda_t ty_map' in
            let thm = inst_fun (mk_var (fname, fty)) lambda_t' p in
              map_thm thm

          | "leftEpsilon" ->
            let (p, _) :: _ = parent_thms in
            let pos_l :: _ = int_params in
            let yname :: _ = string_params in
            let ay = at_left pos_l in
            let hay, ty_map = formula_to_hol ay empty_map in
            let hy, _ = tptp_to_hol_untyped (Var yname) ty_map !def_map in
            let hly = mk_abs (hy, hay) in
            let thm = left_epsilon hly hy p in
              map_thm thm

          | "rightEpsilon" ->
            let (p, _) :: _ = parent_thms in
            let t :: _ = term_params in
            let Sequent ([], [a]) :: _ = seq_params in
            let xname :: _ = string_params in
            let ht, ty_map = tptp_to_hol_untyped t empty_map !def_map in
            let ha, ty_map' = formula_to_hol a ty_map in
            let ht' = propagate_unifiers ht ty_map' in
            let hx, _ = tptp_to_hol_typed (Var xname) ty_map' !def_map (type_of ht') in
            let hla = mk_abs (hx, ha) in
            let thm = right_epsilon hla ht' p in
              map_thm thm

          (* LEVEL 2 STEPS ----------------------------------------------------------------- *)

          | "congruence" ->
            let hant, ty_map = formula_list_to_hol ant empty_map in
            let hsuc, ty_map' = formula_list_to_hol suc ty_map in
            let hnsuc = List.map mk_neg hsuc in
            let taut = List.fold_right (fun f acc -> mk_imp (f, acc)) (List.append hant hnsuc) `F` in
            let taut_thm = MESON [] taut in 
            let thm = UNDISCH_ALL taut_thm in
              map_thm thm

          | "leftHyp" ->
            (* basically hypothesis but with both formulas on the left *)
            let pos_l :: _ = int_params in
            let an = at_left pos_l in
            let Not a = an in
            let wls = remove an (remove a ant) in
            let wrs = suc in
            let hwls, ty_map = formula_list_to_hol wls empty_map in
            let hwrs, ty_map' = formula_list_to_hol wrs ty_map in
            let ha, _ = formula_to_hol a ty_map' in
            let thm = weaken hwls hwrs (hypothesis ha) in
              map_thm thm

          | "leftNotAnd" ->
            let pos_l :: _ = int_params in
            let (pl, _) :: (pr, _) :: _ = parent_thms in
            let na_and_b = at_left pos_l in
            let hnab, _ = formula_to_hol na_and_b empty_map in
            let hab = dest_neg hnab in
            let (ha, hb) = dest_conj hab in
            let thm = right_and ha hb pl pr in
              map_thm thm

          | "leftNotOr" -> 
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let na_or_b = at_left pos_l in
            let hnaob, _ = formula_to_hol na_or_b empty_map in
            let haob = dest_neg hnaob in
            let (ha, hb) = dest_disj haob in
            let thm = right_or ha hb p in
              map_thm thm

          | "leftNotImplies" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let na_imp_b = at_left pos_l in
            let hnib, _ = formula_to_hol na_imp_b empty_map in
            let hib = dest_neg hnib in
            let (ha, hb) = dest_imp hib in
            let thm = right_implies ha hb p in
              map_thm thm

          | "leftNotIff" ->
            let pos_l :: _ = int_params in
            let (pl, _) :: (pr, _) :: _ = parent_thms in
            let na_iff_b = at_left pos_l in
            let hnib, _ = formula_to_hol na_iff_b empty_map in
            let hib = dest_neg hnib in
            let (ha, hb) = dest_iff hib in
            let thm = right_iff ha hb pl pr in
              map_thm thm

          | "leftNotNot" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let na = at_left pos_l in
            let hna, _ = formula_to_hol na empty_map in
            let ha = dest_neg hna in
            let thm = left_not hna (right_not ha p) in
              map_thm thm

          | "leftNotEx" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let t :: _ = term_params in
            let na_ex_a = at_left pos_l in
            let hnea, ty_map = formula_to_hol na_ex_a empty_map in
            let tty = type_of (fst (dest_exists (dest_neg hnea))) in
            let ht, ty_map' = tptp_to_hol_typed t ty_map !def_map tty in
            let hexa = dest_neg hnea in
            let thm = right_ex (propagate_unifiers hexa ty_map') ht p in
              map_thm thm

          | "leftNotAll" ->
            let pos_l :: _ = int_params in
            let (p, _) :: _ = parent_thms in
            let y :: _ = string_params in
            let na_all_a = at_left pos_l in
            let hnaa, ty_map = formula_to_hol na_all_a empty_map in
            let haa = dest_neg hnaa in
            let (x, _) = dest_forall haa in
            let xty = type_of x in
            let hy, _ = tptp_to_hol_typed (Var y) ty_map !def_map xty in
            let thm = right_all haa hy p in
              map_thm thm

          | _ -> 
            failwith (Printf.sprintf "reconstruct_proof: unknown inference rule %s" rule))

        with 
            Invalid_argument _ -> failwith (Printf.sprintf "reconstruct_proof: no inference data found for step %s" n)
          | Failure s -> 
            let source, _ = Option.get a in
            let Inference (rule, _, _) = source in
              failwith (
                let thms = String.concat "\n" (List.map (fun (name, (t, _)) -> name ^ (string_of_thm t)) acc) in
                  Printf.sprintf "reconstruct_proof: step %s role %s step %s --- error: %s\nProved:\n%s" n role rule s thms
                )
        )
    in

    let thm_map = List.fold_left reconstruct_proof' [] scps in

    List.map (fun x -> fst (snd x)) thm_map;;

  (*
    Given a term `concl`, and a list of theorems `proofs`, choose the first theorem
    that proves `[] |- concl` and return it (after appropriate recovery from proof
    of contradiction).

        [...  ant, ¬concl |- ⊥  ...]
    ---------------------------------
            ant |- concl
  *)
  let choose_proof (proofs: thm list) (ant: term list) (concl: term) : thm option =
    let _ = Printf.printf "\nProved thms: %s" (String.concat "\n" (List.map string_of_thm proofs)) in
    let nterm = mk_neg concl in
    let expected_terms = (mk_neg concl) :: ant in
    let term_count = List.length expected_terms in
    let matches_seq (th: thm) = 
      let hyps = Hol.hyp th in
        (List.for_all (fun t -> List.exists (aconv t) expected_terms) hyps) &&
        (List.length hyps = term_count) && 
        (Hol.concl th = `F`)
    in
    let thm_opt = List.find_opt matches_seq proofs in
      Option.map (restore_right concl) thm_opt;;
  
  let sctptp_tac (cmd_constr: string -> string -> string) (err_constr: string) (axs: thm list) (ant: term list) (concl: term) : thm =
    let input_file_name = Filename.temp_file "holl_tptp_" ".p" in
    let output_file_name = Filename.temp_file "holl_tptp_" "_sol.p" in 
    let cmd = cmd_constr input_file_name output_file_name in
    let problem_string, ax_map = emit_problem axs ant concl in
    let oc = open_out input_file_name in
    Printf.fprintf oc "%s\n" problem_string; 
    close_out oc;
    let res = Sys.command cmd in
    if res != 0 then
      failwith (Printf.sprintf "sctptp_tac (err %d): %s" res err_constr)
    else
    let ic = open_in output_file_name in
    let lexbuf = Lexing.from_channel ic in
    let proof_steps = Tptpparser.tptp_file Tptplexer.tokenize lexbuf in
    let proof_thms = reconstruct_proof ax_map proof_steps in
    (* finally, pick out a theorem that actually proved the tautology *)
    let proof_opt = choose_proof proof_thms ant concl in
    match proof_opt with
      | Some thm -> thm
      | None -> failwith "sctptp_tac: internal error --- no proof step matched the input \n"
    ;;

  let EGG = 
    let egg_constr =
      fun input_file output_file -> Printf.sprintf "/workspaces/ubuntu/egg-sc-tptp --level1 %s %s > /dev/null 2>&1" input_file output_file 
    in
    let egg_err = "egg failed to prove the conjecture" in
      sctptp_tac egg_constr egg_err;;

  let GOELAND =
    let gld_constr =
      fun input_file output_file -> 
        let oseq = (String.to_seq output_file) in
        let suffixseq = Seq.take (Seq.length oseq - 2) oseq in
        let ofile = (String.of_seq suffixseq) in
        Printf.sprintf "/workspaces/ubuntu/goeland_linux_release -otptp -wlogs -no_id -quoted_pred -proof_file=%s %s > /dev/null 2>&1" ofile input_file
    in
    let gld_err = "Goeland failed to prove the conjecture" in
      sctptp_tac gld_constr gld_err;;

  module Tptp_tac = struct
    let sctptp_tac = sctptp_tac;;
    let EGG = EGG;;
    let GOELAND = GOELAND;;
  end;;
end;;

open Tptp_tac.Tptp_tac;;
