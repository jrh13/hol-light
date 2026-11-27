(* ========================================================================= *)
(* Intuitionistic theorem prover (complete for propositional fragment).      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

needs "tactics.ml";;

(* ------------------------------------------------------------------------- *)
(* Accept a theorem modulo unification.                                      *)
(* ------------------------------------------------------------------------- *)

let UNIFY_ACCEPT_TAC (mvs:term list) (th:thm):tactic =
  fun (asl,w) ->
    let insts = term_unify mvs (concl th) w in
    ([],insts),[],
    let th' = INSTANTIATE insts th in
    fun i [] -> INSTANTIATE i th';;

(* REFL version of UNIFY_ACCEPT_TAC.
   The conclusion ust be `expr = x` where x is a meta variable.
   It can be `expr = f x y z` where f is a meta variable as well.
*)
let UNIFY_REFL_TAC: tactic =
  fun (asl,w:goal) ->
    let w_lhs,w_rhs = dest_eq w in
    if is_var w_rhs then
      if vfree_in w_rhs w_lhs then
        failwith ("UNIFY_REFL_TAC: failed: `" ^ (string_of_term w) ^ "`")
      else
        UNIFY_ACCEPT_TAC [w_rhs] (REFL w_lhs) (asl,w)
    else
      let constr,rargs = strip_comb w_rhs in
      if not (is_var constr) then failwith "UNIFY_REFL_TAC: not variable" else
      if vfree_in constr w_lhs then
        failwith ("UNIFY_REFL_TAC: failed: `" ^ (string_of_term w) ^ "`")
      else
        (* replace non-variable arguments of the RHS function with temporary
           variables, distinct from each other and from those of the goal. *)
        let rargs_vars = map2
          (fun v gv -> if is_var v then v else
            let _ = Printf.printf
              "UNIFY_REFL_TAC: warning: this isn't var: %s\n"
              (string_of_term v) in gv)
          rargs (genvars [w] (map type_of rargs)) in
        let f = list_mk_abs (rargs_vars,w_lhs) in
        let the_goal = mk_eq (w_lhs, list_mk_comb (f,rargs)) in
        let th = prove(the_goal,
          CONV_TAC (RAND_CONV (DEPTH_CONV BETA_CONV)) THEN
          REFL_TAC) in
        UNIFY_ACCEPT_TAC [constr] th (asl,w);;

(* ------------------------------------------------------------------------- *)
(* The actual prover, as a tactic. The metavariables are made by gv, which   *)
(* numbers them upwards from the genvar_index of the initial goal (with the  *)
(* hypotheses of its assumptions). Every goal of the search is made from     *)
(* that goal and these metavariables, so they are distinct from everything   *)
(* they meet. Since the tactic solves the goal completely, it need not       *)
(* return them or their instantiation, which could otherwise reach other     *)
(* goals of an enclosing proof.                                              *)
(* ------------------------------------------------------------------------- *)

let ITAUT_TAC =
  let CONJUNCTS_THEN' ttac cth =
    ttac(CONJUNCT1 cth) THEN ttac(CONJUNCT2 cth) in
  let IMPLICATE t =
    let th1 = AP_THM NOT_DEF (dest_neg t) in
    CONV_RULE (RAND_CONV BETA_CONV) th1 in
  let RIGHT_REVERSIBLE_TAC = FIRST
   [CONJ_TAC;                                                     (* and     *)
    GEN_TAC;                                                      (* forall  *)
    DISCH_TAC;                                                    (* implies; not *)
    EQ_TAC]                                                       (* iff     *)
  and LEFT_REVERSIBLE_TAC th gl = tryfind (fun ttac -> ttac th gl)
   [CONJUNCTS_THEN' ASSUME_TAC;                                   (* and    *)
    DISJ_CASES_TAC;                                               (* or     *)
    CHOOSE_TAC;                                                   (* exists *)
    (fun th -> ASSUME_TAC (EQ_MP (IMPLICATE (concl th)) th));     (* not    *)
    (CONJUNCTS_THEN' MP_TAC o uncurry CONJ  o EQ_IMP_RULE)]       (* iff    *)
  in
  let rec ITAUT_TAC gv mvs n gl =
    if n <= 0 then failwith "ITAUT_TAC: Too deep" else
    ((FIRST_ASSUM (UNIFY_ACCEPT_TAC mvs)) ORELSE
     (ACCEPT_TAC TRUTH) ORELSE
     (FIRST_ASSUM CONTR_TAC) ORELSE
     (RIGHT_REVERSIBLE_TAC THEN TRY (ITAUT_TAC gv mvs n)) ORELSE
     (FIRST_X_ASSUM LEFT_REVERSIBLE_TAC THEN TRY(ITAUT_TAC gv mvs n)) ORELSE
     (FIRST_X_ASSUM(fun th -> ASSUME_TAC th THEN
       (let v = gv(type_of(fst(dest_forall(concl th)))) in
        META_SPEC_TAC v th THEN
        ITAUT_TAC gv (v::mvs) (n - 2) THEN NO_TAC))) ORELSE
     (DISJ1_TAC THEN ITAUT_TAC gv mvs n THEN NO_TAC) ORELSE
     (DISJ2_TAC THEN ITAUT_TAC gv mvs n THEN NO_TAC) ORELSE
     (fun gl -> let v = gv(type_of(fst(dest_exists(snd gl)))) in
                (X_META_EXISTS_TAC v THEN
                 ITAUT_TAC gv (v::mvs) (n - 2) THEN NO_TAC) gl) ORELSE
     (FIRST_ASSUM(fun th -> SUBGOAL_THEN (fst(dest_imp(concl th)))
                                      (fun ath -> ASSUME_TAC (MP th ath)) THEN
                           ITAUT_TAC gv mvs (n - 1) THEN NO_TAC))) gl in
  let rec ITAUT_ITERDEEP_TAC gv n gl =
    remark ("Searching with limit "^(string_of_int n));
    ((ITAUT_TAC gv [] n THEN NO_TAC) ORELSE
     ITAUT_ITERDEEP_TAC gv (n + 1)) gl in
  fun gl ->
    let next = ref (-1) in
    let gv ty =
      let n = if !next >= 0 then !next else genvar_index_goal gl in
      next := n + 1; mk_genvar(n,ty) in
    let _,gls,just = ITAUT_ITERDEEP_TAC gv 0 gl in
    null_meta,gls,just;;

(* ------------------------------------------------------------------------- *)
(* Alternative interface.                                                    *)
(* ------------------------------------------------------------------------- *)

let ITAUT tm = prove(tm,ITAUT_TAC);;
