(* ========================================================================= *)
(* Mizar-style proofs integrated with the HOL goalstack.                     *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(* ========================================================================= *)

let old_parse_term = parse_term;;

(* ------------------------------------------------------------------------- *)
(* This version of CHOOSE is more convenient to "itlist".                    *)
(* ------------------------------------------------------------------------- *)

let IMP_CHOOSE_RULE =
  let P = `P:A->bool`
  and Q = `Q:bool`
  and pth = prove
   (`(!x:A. P x ==> Q) ==> ((?) P ==> Q)`,
    GEN_REWRITE_TAC (RAND_CONV o LAND_CONV o RAND_CONV) [GSYM ETA_AX] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM]) in
  fun v th ->
    let ant,con = dest_imp (concl th) in
    let pred = mk_abs(v,ant) in
    let tm = concl th in
    let q = rand tm in
    let th1 = BETA_CONV(mk_comb(pred,v)) in
    let th2 = PINST [type_of v,aty] [pred,P; q,Q] pth in
    let th3 = AP_THM (AP_TERM (rator(rator tm)) th1) q in
    let th4 = GEN v (EQ_MP (SYM th3) th) in
    MP th2 th4;;

(* ------------------------------------------------------------------------- *)
(* Some preterm operations we need.                                          *)
(* ------------------------------------------------------------------------- *)

let rec split_ppair ptm =
  match ptm with
    Combp(Combp(Varp(",",dpty),ptm1),ptm2) -> ptm1::(split_ppair ptm2)
  | _ -> [ptm];;

let pmk_conj(ptm1,ptm2) =
  Combp(Combp(Varp("/\\",dpty),ptm1),ptm2);;

let pmk_exists(v,ptm) =
  Combp(Varp("?",dpty),Absp(v,ptm));;

(* ------------------------------------------------------------------------- *)
(* Typecheck a preterm into a term in an environment of (typed) variables.   *)
(* ------------------------------------------------------------------------- *)

let typecheck_in_env env ptm =
  let penv = itlist
    (fun v acc -> let n,ty = dest_var v in (n,pretype_of_type ty)::acc)
    env [] in
  (term_of_preterm o retypecheck penv) ptm;;

(* ------------------------------------------------------------------------- *)
(* Converts a labelled preterm (using "and"s) into a single conjunction.     *)
(* ------------------------------------------------------------------------- *)

let delabel lfs = end_itlist (curry pmk_conj) (map snd lfs);;

(* ------------------------------------------------------------------------- *)
(* These special constants are replaced by useful bits when encountered:     *)
(*                                                                           *)
(*  thesis       -- Current thesis (i.e. conclusion of goal).                *)
(*                                                                           *)
(*  antecedent   -- antecedent of goal, if applicable                        *)
(*                                                                           *)
(* contradiction -- falsity                                                  *)
(*                                                                           *)
(*  ...          -- Right hand side of previous conclusion.                  *)
(* ------------------------------------------------------------------------- *)

let thesis = new_definition
  `thesis = F`;;

let antecedent = new_definition
  `antecedent = F`;;

let contradiction = new_definition
  `contradiction = F`;;

let iter_rhs = new_definition
  `... = @x:A. F`;;

(* ------------------------------------------------------------------------- *)
(* This function performs the replacement, and typechecks in current env.    *)
(*                                                                           *)
(* The replacement of "..." is done specially, since it also adds a "then".  *)
(* ------------------------------------------------------------------------- *)

let mizarate_term =
  let atm = `antecedent`
  and ttm = `thesis`
  and ctm = `contradiction` in
  let f_tm = `F` in
  let filter_env fvs =
    let env1 = map dest_var fvs in
    let sizes = map
      (fun (v,_) -> v,length (filter ((=) v o fst) env1)) env1 in
    let env2 = filter (fun (v,_) -> assoc v sizes = 1) env1 in
    map mk_var env2 in
  let goal_lconsts (asl,w) =
    itlist (union o frees o concl o snd) asl (frees w) in
  fun (asl,w as gl) ptm ->
    let lconsts = goal_lconsts gl in
    let tm = typecheck_in_env (filter_env lconsts) ptm in
    let ant = try fst(dest_imp w) with Failure _ -> atm in
    subst [w,ttm; ant,atm; f_tm,ctm] tm;;

(* ------------------------------------------------------------------------- *)
(* The following is occasionally useful as a hack.                           *)
(* ------------------------------------------------------------------------- *)

let LIMITED_REWRITE_CONV =
  let LIMITED_ONCE_REWRITE_CONV ths =
    GEN_REWRITE_CONV ONCE_DEPTH_CONV ths THENC
    GENERAL_REWRITE_CONV true TOP_DEPTH_CONV (basic_net()) [] in
  fun n ths tm ->
        funpow n (CONV_RULE(RAND_CONV(LIMITED_ONCE_REWRITE_CONV ths)))
                 (REFL tm);;

(* ------------------------------------------------------------------------- *)
(* The default prover.                                                       *)
(* ------------------------------------------------------------------------- *)

let DEFAULT_PROVER =
  let FREEZE_THENL fn ths x =
    let ths' = map (ASSUME o concl) ths in
    let th = fn ths' x in
    itlist PROVE_HYP ths th in
  let REWRITE_PROVER ths tm =
    if length ths < 2 then
          EQT_ELIM(LIMITED_REWRITE_CONV 3 ths tm)
        else
           let ths' = tl ths in
           let th' = CONV_RULE (LIMITED_REWRITE_CONV 4 ths') (hd ths) in
           EQT_ELIM(LIMITED_REWRITE_CONV 4 (th'::ths') tm) in
  fun ths tm ->
    let sths = itlist (union o CONJUNCTS) ths [] in
    try prove(tm,MAP_FIRST MATCH_ACCEPT_TAC sths)
    with Failure _ -> try
        FREEZE_THENL REWRITE_PROVER ths tm
    with Failure _ ->
        prove(tm,GEN_MESON_TAC 0 30 1 ths);;

let default_prover = ref DEFAULT_PROVER;;

let prover_list = ref
  ["rewriting",(fun ths tm -> EQT_ELIM(REWRITE_CONV ths tm))];;

(* ------------------------------------------------------------------------- *)
(*    "arithmetic",(fun ths tm ->                                            *)
(*                    let tm' = itlist (curry mk_imp o concl) ths tm in      *)
(*                    let th = REAL_ARITH tm' in                             *)
(*                    rev_itlist (C MP) ths th);;                            *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Produce a "default" label for various constructs where applicable.        *)
(* ------------------------------------------------------------------------- *)

let default_assumptions = ref false;;

let mklabel s =
  if s = "" && !default_assumptions then "*"
  else s;;

(* ------------------------------------------------------------------------- *)
(* Augment assumptions, throwing away an *unnamed* previous step.            *)
(* ------------------------------------------------------------------------- *)

let augments =
  let augment nw asl =
    if asl = [] then [nw]
    else if fst(hd asl) = "" then nw::(tl asl)
    else nw::asl in
  fun labs th asl ->
    let ths,thl = nsplit CONJ_PAIR (tl labs) th in
    itlist augment (zip (map mklabel labs) (ths@[thl])) asl;;

(* ------------------------------------------------------------------------- *)
(* Wrapper for labels in justification list (use K for preproved theorems).  *)
(* ------------------------------------------------------------------------- *)

let L s asl =
  if s = "" then snd(hd asl) else ((assoc s asl):thm);;

(* ------------------------------------------------------------------------- *)
(* Perform justification, given asl and target.                              *)
(* ------------------------------------------------------------------------- *)

let JUSTIFY (prover,tlist) asl tm =
  let xthms = map (C I asl) tlist in
  let proof_fn =
    if prover = "" then !default_prover
    else assoc prover (!prover_list) in
  let ithms = map snd (filter ((=) "*" o fst) asl) in
  proof_fn (xthms @ ithms) tm;;

(* ------------------------------------------------------------------------- *)
(* Either do justification or split off subproof then call ttac with result. *)
(* ------------------------------------------------------------------------- *)

let JUSTIFY_THEN wtm ((pr,tls) as jdata) ttac (asl,w as gl) =
  if pr = "proof" then
    SUBGOAL_THEN wtm ttac gl
  else
    let wth = JUSTIFY jdata asl wtm in
    ttac wth gl;;

(* ------------------------------------------------------------------------- *)
(* Utilise a conclusion.                                                     *)
(* ------------------------------------------------------------------------- *)

let (MIZAR_CONCLUSION_TAC:thm_tactic) =
  let t_tm = `T` in
  let CONJ_ASSOC_RULE =
    EQT_ELIM o
    GEN_REWRITE_RULE RAND_CONV [EQT_INTRO(SPEC_ALL EQ_REFL)] o
    PURE_REWRITE_CONV[GSYM CONJ_ASSOC] in
  fun th (asl,w as gl) ->
    let cjs = conjuncts(concl th) in
    let cjs1,cjs2 = chop_list(length cjs) (conjuncts w) in
    if cjs2 = [] then
      let th' = EQ_MP (CONJ_ASSOC_RULE(mk_eq(concl th,w))) th in
      null_meta,[asl,t_tm],fun i _ -> INSTANTIATE i th'
    else
      let w1 = list_mk_conj cjs1
      and w2 = list_mk_conj cjs2 in
      let w12 = mk_conj(w1,w2) in
      let th' = EQ_MP (CONJ_ASSOC_RULE(mk_eq(concl th,w1))) th in
      let wth = CONJ_ASSOC_RULE(mk_eq(w,w12)) in
      (SUBST1_TAC wth THEN CONJ_TAC THENL [ACCEPT_TAC th'; ALL_TAC]) gl;;

(* ------------------------------------------------------------------------- *)
(* Transitivity chain stuff; store a list of useful transitivity theorems.   *)
(* ------------------------------------------------------------------------- *)

let mizar_transitivity_net = ref empty_net;;

let add_mizar_transitivity_theorem th =
  let pat = fst(dest_imp(snd(strip_forall(concl th)))) in
  mizar_transitivity_net :=
    enter [] (pat,MATCH_MP th) (!mizar_transitivity_net);;

let TRANSITIVITY_CHAIN th1 th2 ttac =
  let tm1 = concl th1
  and tm2 = concl th2 in
  let th =
    if is_eq tm1 then
      EQ_MP (SYM (AP_THM (AP_TERM (rator(rator tm2)) th1) (rand tm2))) th2
    else if is_eq tm2 then
      EQ_MP (AP_TERM (rator tm1) th2) th1
    else
      let th12 = CONJ th1 th2 in
      tryfind (fun rule -> rule th12)
        (lookup (concl th12) (!mizar_transitivity_net)) in
  ttac th;;

(* ------------------------------------------------------------------------- *)
(* Perform terminal or initial step.                                         *)
(* ------------------------------------------------------------------------- *)

let MIZAR_SUBSTEP_TAC =
  fun labs thm (asl,w) ->
    let asl' = augments labs thm asl in
    null_meta,[asl',w],
    K(function [th] -> PROVE_HYP thm th | _ -> fail());;

let MIZAR_BISTEP_TAC =
  fun termflag labs jth ->
    if termflag then
      MIZAR_SUBSTEP_TAC labs jth THEN
      MIZAR_CONCLUSION_TAC jth
    else
      MIZAR_SUBSTEP_TAC labs jth;;

let MIZAR_STEP_TAC =
  fun termflag lfs (pr,tls as jdata) (asl,w as gl) ->
    let tm = mizarate_term gl (delabel lfs) in
    if try fst(dest_const(lhand tm)) = "..." with Failure _ -> false then
      let thp = snd(hd asl) in
      let lhd = rand(concl thp) in
      let tm' = mk_comb(mk_comb(rator(rator tm),lhd),rand tm) in
      JUSTIFY_THEN tm' (pr,tls)
        (fun th -> TRANSITIVITY_CHAIN thp th
                      (MIZAR_BISTEP_TAC termflag (map fst lfs))) gl
    else
      JUSTIFY_THEN tm (pr,tls)
        (MIZAR_BISTEP_TAC termflag (map fst lfs)) gl;;

(* ------------------------------------------------------------------------- *)
(* Perform an "end": finish the trivial goal.                                *)
(* ------------------------------------------------------------------------- *)

let MIZAR_END_TAC = ACCEPT_TAC TRUTH;;

(* ------------------------------------------------------------------------- *)
(* Perform "assume <lform>"                                                  *)
(* ------------------------------------------------------------------------- *)

let (MIZAR_ASSUME_TAC: (string * preterm) list -> tactic) =
  let f_tm = `F`
  and CONTRA_HACK = CONV_RULE(REWR_CONV(TAUT `(~p ==> F) <=> p`)) in
  fun lfs (asl,w as gl) ->
    let tm = mizarate_term gl (delabel lfs) in
    if try aconv (dest_neg tm) w with Failure _ -> false then
      (null_meta,[augments (map fst lfs) (ASSUME tm) asl,f_tm],
      (fun i -> function [th] -> CONTRA_HACK(DISCH (instantiate i tm) th)
                       | _ -> fail()))
    else if try aconv tm (fst(dest_imp w)) with Failure _ -> false then
      (null_meta,[augments (map fst lfs) (ASSUME tm) asl,rand w],
      (fun i -> function [th] -> DISCH (instantiate i tm) th
                       | _ -> fail()))
    else failwith "MIZAR_ASSUME_REF: Bad thesis";;

(* ------------------------------------------------------------------------- *)
(* Perform "let <v1>,...,<vn> [be <type>]"                                   *)
(* ------------------------------------------------------------------------- *)

let (MIZAR_LET_TAC: preterm list * hol_type list -> tactic) =
  fun (vlist,tys) (asl,w as gl) ->
    let ty = if tys = [] then type_of(fst(dest_forall w)) else hd tys in
    let pty = pretype_of_type ty in
    let mk_varb v =
       (term_of_preterm o retypecheck []) (Typing(v,pty)) in
    let vs = map mk_varb vlist in
    MAP_EVERY X_GEN_TAC vs gl;;

(* ------------------------------------------------------------------------- *)
(* Perform "take <tm>"                                                       *)
(* ------------------------------------------------------------------------- *)

let (MIZAR_TAKE_TAC: preterm -> tactic) =
  fun ptm (asl,w as gl) ->
    let ptm' = Typing(ptm,pretype_of_type(type_of(fst(dest_exists w)))) in
    let tm = mizarate_term (asl,w) ptm' in
    EXISTS_TAC tm gl;;

(* ------------------------------------------------------------------------- *)
(* Perform "suffices to prove <form> by <just>".                             *)
(* ------------------------------------------------------------------------- *)

let MIZAR_SUFFICES_TAC =
  fun new0 ((pr,tlist) as jdata) (asl,w as gl) ->
    let nw = mizarate_term gl (end_itlist (curry pmk_conj) new0) in
    JUSTIFY_THEN (mk_imp(nw,w)) jdata
      (fun jth (asl,w) ->
         null_meta,[asl,nw],
         (fun i -> function [th] -> MP (INSTANTIATE_ALL i jth) th
                          | _ -> fail())) gl;;

(* ------------------------------------------------------------------------- *)
(* Perform "set <lform>"                                                     *)
(* ------------------------------------------------------------------------- *)

let MIZAR_SET_TAC =
  fun (lab,ptm) (asl,w as gl) ->
    let tm = mizarate_term gl ptm in
    let v,t = dest_eq tm in
    CHOOSE_THEN (fun th -> SUBST_ALL_TAC th THEN
                           LABEL_TAC (mklabel lab) (SYM th))
                (EXISTS(mk_exists(v,mk_eq(t,v)),t) (REFL t)) gl;;

(* ------------------------------------------------------------------------- *)
(* Perform "consider <vars> such that <lform> by <just>".                    *)
(* ------------------------------------------------------------------------- *)

let MIZAR_CONSIDER_TAC =
  fun vars0 lfs ((pr,tls) as jdata) (asl,w as gl) ->
    let ptm = itlist (curry pmk_exists) vars0 (delabel lfs) in
    let etm = mizarate_term gl ptm in
    let vars,tm = nsplit dest_exists vars0 etm in
    JUSTIFY_THEN etm jdata
      (fun jth (asl,w) ->
         null_meta,[augments (map fst lfs) (ASSUME tm) asl,w],
         (fun i -> function [th] -> MP (itlist IMP_CHOOSE_RULE vars
                                   (DISCH (instantiate i tm) th)) jth
                          | _ -> fail())) gl;;

(* ------------------------------------------------------------------------- *)
(* Perform "given <terms> such that <lform>".                                *)
(* ------------------------------------------------------------------------- *)

let MIZAR_GIVEN_TAC =
  fun vars0 lfs (asl,w as gl) ->
    let ant = fst(dest_imp w) in
    let gvars,gbod = nsplit dest_exists vars0 ant in
    let tvars = map2
      (fun p v -> Typing(p,pretype_of_type(snd(dest_var v)))) vars0 gvars in
    let ptm = itlist (curry pmk_exists) tvars (delabel lfs) in
    let etm = mizarate_term gl ptm in
    let vars,tm = nsplit dest_exists vars0 etm in
    if try aconv ant etm with Failure _ -> false then
      null_meta,[augments (map fst lfs) (ASSUME tm) asl,rand w],
      (fun i -> function [th] -> DISCH ant
                     (MP (itlist IMP_CHOOSE_RULE vars
                                 (DISCH (instantiate i tm) th))
                         (ASSUME ant))
                  | _ -> fail())
    else failwith "MIZAR_GIVEN_TAC: Bad thesis";;

(* ------------------------------------------------------------------------- *)
(* Initialize a case split.                                                  *)
(* ------------------------------------------------------------------------- *)

let MIZAR_PER_CASES_TAC =
  fun jdata (asl,w as gl) ->
    null_meta,[gl],
    K(function [th] ->
        let ghyps = itlist (union o hyp o snd) asl [] in
        let rogues = subtract (hyp th) ghyps in
        if rogues = [] then th
        else if tl rogues = [] then
          let thm = JUSTIFY jdata asl (hd rogues) in
          PROVE_HYP thm th
        else failwith "MIZAR_PER_CASES_ATAC: Too many suppositions"
     | _ -> fail());;

(* ------------------------------------------------------------------------- *)
(* Perform a case split. NB! This tactic is not "valid" in the LCF sense.    *)
(* We could make it so, but that would force classical logic!                *)
(* ------------------------------------------------------------------------- *)

let MIZAR_SUPPOSE_TAC =
  fun lfs (asl,w as gl) ->
    let asm = mizarate_term gl (delabel lfs) in
    let ghyps = itlist (union o hyp o snd) asl [] in
    null_meta,
    [augments (map fst lfs) (ASSUME asm) asl,w; gl],
    K(function [th1; th2] ->
       let hyp1 = hyp th1
       and hyp2 = hyp th2 in
       let asm1 = subtract hyp1 ghyps
       and asm2 = subtract hyp2 ghyps in
       if asm1 = [] then th1 else if asm2 = [] then th2
       else if tl asm1 = [] && tl asm2 = [] then
         DISJ_CASES (ASSUME(mk_disj(hd asm1,hd asm2))) th1 th2
       else failwith "MIZAR_SUPPOSE_TAC: Too many suppositions"
     | _ -> fail());;

let MIZAR_SUPPOSE_REF lfs =
  by (MIZAR_SUPPOSE_TAC lfs) o by (TRY MIZAR_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* Terminate a case split.                                                   *)
(* ------------------------------------------------------------------------- *)

let MIZAR_RAW_ENDCASE_TAC =
  let pth = ITAUT `F ==> p`
  and p = `p:bool` in
  fun (asl,w) ->
    let th = UNDISCH (INST [w,p] pth) in
    null_meta,[],fun _ _ -> th;;

let MIZAR_ENDCASE_REF =
  by MIZAR_RAW_ENDCASE_TAC o by (TRY MIZAR_END_TAC);;

(* ------------------------------------------------------------------------- *)
(* Parser-processor for textual version of Mizar proofs.                     *)
(* ------------------------------------------------------------------------- *)

let add_mizar_words,subtract_mizar_words =
  let l =  ["assume"; "take"; "set"; "given"; "such"; "that";
            "proof"; "end"; "consider"; "suffices"; "to"; "show";
            "per"; "cases"; "endcase"; "suppose"; "be";
            "then"; "thus"; "hence"; "by"; "so"] in
  (fun () -> reserve_words l),
  (fun () -> unreserve_words l);;

let parse_preform l =
  let ptm,rst = parse_preterm l in
  let ptm' = Typing(ptm,Ptycon("bool",[])) in
  ptm',rst;;

let parse_fulltype l =
  let pty,rst = parse_pretype l in
  type_of_pretype pty,rst;;

let parse_ident l =
  match (hd l) with
    Ident n -> n,tl l
  | _ -> raise Noparse;;

let parse_string l =
  match (hd l) with
    Ident n -> n,tl l
  | Resword n -> n,tl l;;

let rec parse_lform oldlab l =
  match l with
    (Ident n)::(Resword ":")::rst ->
        if oldlab = "" then parse_lform n rst
        else failwith "Too many labels"
  | _ -> let fm,rst = parse_preform l in (oldlab,fm),rst;;

let parse_lforms oldlab =
  listof (parse_lform oldlab) (a (Resword "and")) "labelled formula";;

let parse_just tlink l =
  if l = [] then
    if tlink then ("",[L""]),l
    else ("",[]),l else
  match (hd l) with
    Resword "by" ->
        let pot,rem = parse_string (tl l) in
        if rem = [] || hd rem <> Ident "," && hd rem <> Ident "with" then
          if can (assoc pot) (!prover_list) then
            (pot,if tlink then [L""] else []),rem
          else
            ("",if tlink then [L""; L pot] else [L pot]),rem
        else if hd rem = Ident "," then
          let oths,rst = listof parse_string (a (Ident ",")) "theorem name"
           (tl rem) in
          let ths = if tlink then ""::pot::oths else pot::oths in
          ("",map L ths),rst
        else
          let oths,rst = listof parse_string (a (Ident ",")) "theorem name"
            (tl rem) in
          let ths = if tlink then ""::oths else oths in
          (pot,map L ths),rst
  | Resword "proof" ->
        ("proof",[]),tl l
  | _ ->
        if tlink then ("",[L""]),l
        else ("",[]),l;;

let rec parse_step tlink l =
   (a (Resword "assume") ++ parse_lforms ""
      >> (by o MIZAR_ASSUME_TAC o snd)
 ||| (a (Resword "let") ++ (parse_preterm >> split_ppair) ++
      possibly (a (Resword "be") ++ parse_fulltype >> snd)
      >> (fun ((_,vnames),ty) -> by (MIZAR_LET_TAC (vnames,ty))))
 ||| (a (Resword "take") ++ parse_preterm
      >> (by o MIZAR_TAKE_TAC o snd))
 ||| (a (Resword "set") ++ parse_lforms ""
      >> (itlist (by o MIZAR_SET_TAC) o snd))
 ||| (a (Resword "consider") ++
      (parse_preterm >> split_ppair) ++
      a (Resword "such") ++
      a (Resword "that") ++
      parse_lforms "" ++
      parse_just tlink
      >> (fun (((((_,vars),_),_),lf),jst) -> by (MIZAR_CONSIDER_TAC vars lf jst)))
 ||| (a (Resword "given") ++
      (parse_preterm >> split_ppair) ++
      a (Resword "such") ++
      a (Resword "that") ++
      parse_lforms ""
      >> (fun ((((_,vars),_),_),lf) -> by (MIZAR_GIVEN_TAC vars lf)))
 ||| (a (Resword "suffices") ++
      a (Resword "to") ++
      a (Resword "show") ++
      parse_lforms "" ++
      parse_just tlink
      >> (fun ((((_,_),_),lf),jst) -> by (MIZAR_SUFFICES_TAC (map snd lf) jst)))
 ||| (a (Resword "per") ++
      a (Resword "cases") ++
      parse_just tlink
      >> (fun ((_,_),jst) -> by (MIZAR_PER_CASES_TAC jst)))
 ||| (a (Resword "suppose") ++
      parse_lforms ""
      >> (fun (_,lf) -> MIZAR_SUPPOSE_REF lf))
 ||| (a (Resword "endcase")
      >> K MIZAR_ENDCASE_REF)
 ||| (a (Resword "end")
      >> K (by MIZAR_END_TAC))
 ||| (a (Resword "then") ++ parse_step true
      >> snd)
 ||| (a (Resword "so") ++ parse_step true
      >> snd)
 ||| (a (Resword "hence") ++
      parse_lforms "" ++
      parse_just true
      >> (fun ((_,lf),jst) -> by (MIZAR_STEP_TAC true lf jst)))
 ||| (a (Resword "thus") ++
      parse_lforms "" ++
      parse_just tlink
      >> (fun ((_,lf),jst) -> by (MIZAR_STEP_TAC true lf jst)))
 ||| (parse_lforms "" ++ parse_just tlink
      >> (fun (lf,jst) -> by (MIZAR_STEP_TAC false lf jst)))) l;;

(* ------------------------------------------------------------------------- *)
(* From now on, quotations evaluate to preterms.                             *)
(* ------------------------------------------------------------------------- *)

let run_steps lexemes =
  let rec compose_steps lexemes gs =
    if lexemes = [] then gs else
    let rf,rest = parse_step false lexemes in
    let gs' = rf gs in
    if rest <> [] && hd rest = Resword ";" then compose_steps (tl rest) gs'
    else compose_steps rest gs' in
  refine (compose_steps lexemes);;

(* ------------------------------------------------------------------------- *)
(* Include some theorems.                                                    *)
(* ------------------------------------------------------------------------- *)

do_list add_mizar_transitivity_theorem
  [LE_TRANS; LT_TRANS; LET_TRANS; LTE_TRANS];;

do_list add_mizar_transitivity_theorem
  [INT_LE_TRANS; INT_LT_TRANS; INT_LET_TRANS; INT_LTE_TRANS];;

do_list add_mizar_transitivity_theorem
  [REAL_LE_TRANS; REAL_LT_TRANS; REAL_LET_TRANS; REAL_LTE_TRANS];;

do_list add_mizar_transitivity_theorem
  [SUBSET_TRANS; PSUBSET_TRANS; PSUBSET_SUBSET_TRANS; SUBSET_PSUBSET_TRANS];;

(* ------------------------------------------------------------------------- *)
(* Simple example: Knaster-Tarski fixpoint theorem.                          *)
(* ------------------------------------------------------------------------- *)

add_mizar_words();;

hide_constant "<=";;

(*** Set up goal ***)

g `!f. (!x y. x <= y /\ y <= x ==> (x = y)) /\
     (!x y z. x <= y /\ y <= z ==> x <= z) /\
     (!x y. x <= y ==> f x <= f y) /\
     (!X. ?s:A. (!x. x IN X ==> s <= x) /\
                (!s'. (!x. x IN X ==> s' <= x) ==> s' <= s))
     ==> ?x. f x = x`;;

(*** Start parsing quotations as Mizar directives ***)

let parse_term = run_steps o lex o explode;;

(*** Label the external facts needed ***)

e(LABEL_TAC "IN_ELIM_THM" IN_ELIM_THM);;
e(LABEL_TAC "BETA_THM" BETA_THM);;

(*** The proof itself ***)

 `let f be A->A;
  assume L:antecedent;
  antisymmetry: (!x y. x <= y /\ y <= x ==> (x = y)) by L;
  transitivity: (!x y z. x <= y /\ y <= z ==> x <= z) by L;
  monotonicity: (!x y. x <= y ==> f x <= f y) by L;
  least_upper_bound:
      (!X. ?s:A. (!x. x IN X ==> s <= x) /\
                 (!s'. (!x. x IN X ==> s' <= x) ==> s' <= s)) by L;
  set Y_def: Y = {b | f b <= b};
  Y_thm: !b. b IN Y <=> f b <= b by Y_def,IN_ELIM_THM,BETA_THM;
  consider a such that
      lub: (!x. x IN Y ==> a <= x) /\
           (!a'. (!x. x IN Y ==> a' <= x) ==> a' <= a)
      by least_upper_bound;
  take a;
  !b. b IN Y ==> f a <= b
  proof
    let b be A;
    assume b_in_Y: b IN Y;
    then L0: f b <= b by Y_thm;
    a <= b by b_in_Y, lub;
    so f a <= f b by monotonicity;
    hence f a <= b by L0, transitivity;
    end;
  so Part1: f(a) <= a by lub;
  so f(f(a)) <= f(a) by monotonicity;
  so f(a) IN Y by Y_thm;
  so a <= f(a) by lub;
  hence thesis by Part1, antisymmetry;
end`;;

(*** Get the theorem ***)

top_thm();;

(* ------------------------------------------------------------------------- *)
(* Back to normal.                                                           *)
(* ------------------------------------------------------------------------- *)

let parse_term = old_parse_term;;
