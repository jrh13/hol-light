(* open satTools dimacsTools SatSolvers minisatResolve
   satCommonTools minisatParse satScript def_cnf *)

(*
for interactive use:

   #load "str.cma";;
   #use "def_cnf.ml";;
   #use "satCommonTools.ml";;
   #use "dimacsTools.ml";;
   #use "SatSolvers.ml";;
   #use "satScript.ml";;
   #use "satTools.ml";;
   #use "minisatParse.ml";;
   #use "minisatResolve.ml";;
   #use "minisatProve.ml";;
   #use "taut.ml";;
*)
(* ------------------------------------------------------------------------- *)
(* Flag to (de-)activate debugging facilities.                               *)
(* ------------------------------------------------------------------------- *)

let sat_debugging = ref false;;

(* ------------------------------------------------------------------------- *)
(* Split up a theorem according to conjuncts, in a general sense.            *)
(* ------------------------------------------------------------------------- *)

let GCONJUNCTS =
  let [pth_ni1; pth_ni2; pth_no1; pth_no2; pth_an1; pth_an2; pth_nn] =
    (map UNDISCH_ALL o CONJUNCTS o TAUT)
    `(~(p ==> q) ==> p) /\
     (~(p ==> q) ==> ~q) /\
     (~(p \/ q) ==> ~p) /\
     (~(p \/ q) ==> ~q) /\
     (p /\ q ==> p) /\
     (p /\ q ==> q) /\
     (~ ~p ==> p)` in
  let p_tm = concl pth_an1 and q_tm = concl pth_an2 in
  let rec GCONJUNCTS th acc =
    match (concl th) with
      Comb(Const("~",_),Comb(Comb(Const("==>",_),p),q)) ->
       GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_ni1))
                  (GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_ni2))
                              acc)
    | Comb(Const("~",_),Comb(Comb(Const("\\/",_),p),q)) ->
       GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_no1))
                  (GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_no2))
                              acc)
    | Comb(Comb(Const("/\\",_),p),q) ->
       GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_an1))
                  (GCONJUNCTS (PROVE_HYP th (INST [p,p_tm; q,q_tm] pth_an2))
                              acc)
    | Comb(Const("~",_),Comb(Const("~",_),p)) ->
          GCONJUNCTS (PROVE_HYP th (INST [p,p_tm] pth_nn)) acc
    | _ -> th::acc in
  fun th -> GCONJUNCTS th [];;

(* ------------------------------------------------------------------------- *)
(* Generate fresh variable names (could just use genvars).                   *)
(* ------------------------------------------------------------------------- *)

let propvar i = mk_var("x"^string_of_int i,bool_ty);;

(* ------------------------------------------------------------------------- *)
(* Set up the basic definitional arrangement.                                *)
(* ------------------------------------------------------------------------- *)

let rec localdefs tm (n,defs,lfn) =
  if is_neg tm then
    let n1,v1,defs1,lfn1 = localdefs (rand tm) (n,defs,lfn) in
    let tm' = mk_neg v1 in
    try (n1,apply defs1 tm',defs1,lfn1) with Failure _ ->
    let n2 = n1 + 1 in
    let v2 = propvar n2 in
    n2,v2,(tm' |-> v2) defs1,(v2 |-> tm) lfn1
  else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
    let n1,v1,defs1,lfn1 = localdefs (lhand tm) (n,defs,lfn) in
    let n2,v2,defs2,lfn2 = localdefs (rand tm) (n1,defs1,lfn1) in
    let tm' = mk_comb(mk_comb(rator(rator tm),v1),v2) in
    try (n2,apply defs2 tm',defs2,lfn2) with Failure _ ->
    let n3 = n2 + 1 in
    let v3 = propvar n3 in
    n3,v3,(tm' |-> v3) defs2,(v3 |-> tm) lfn2
  else try (n,apply defs tm,defs,lfn) with Failure _ ->
       let n1 = n + 1 in
       let v1 = propvar n1 in
       n1,v1,(tm |-> v1) defs,(v1 |-> tm) lfn;;

(* ------------------------------------------------------------------------- *)
(* Just translate to fresh variables, but otherwise leave unchanged.         *)
(* ------------------------------------------------------------------------- *)

let rec transvar (n,tm,vdefs,lfn) =
  if is_neg tm then
    let n1,tm1,vdefs1,lfn1 = transvar (n,rand tm,vdefs,lfn) in
    n1,mk_comb(rator tm,tm1),vdefs1,lfn1
  else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
    let n1,tm1,vdefs1,lfn1 = transvar (n,lhand tm,vdefs,lfn) in
    let n2,tm2,vdefs2,lfn2 = transvar (n1,rand tm,vdefs1,lfn1) in
    n2,mk_comb(mk_comb(rator(rator tm),tm1),tm2),vdefs2,lfn2
  else try n,apply vdefs tm,vdefs,lfn with Failure _ ->
       let n1 = n + 1 in
       let v1 = propvar n1 in
       n1,v1,(tm |-> v1) vdefs,(v1 |-> tm) lfn;;

(* ------------------------------------------------------------------------- *)
(* Flag to choose whether to exploit existing conjunctive structure.         *)
(* ------------------------------------------------------------------------- *)

let exploit_conjunctive_structure = ref true;;

(* ------------------------------------------------------------------------- *)
(* Check if something is clausal (slightly stupid).                          *)
(* ------------------------------------------------------------------------- *)

let is_literal tm = is_var tm || is_neg tm && is_var(rand tm);;

let is_clausal tm =
  let djs = disjuncts tm in
  forall is_literal djs && list_mk_disj djs = tm;;

(* ------------------------------------------------------------------------- *)
(* Now do the definitional arrangement but not wastefully at the top.        *)
(* ------------------------------------------------------------------------- *)

let definitionalize =
  let transform_imp =
    let pth = TAUT `(p ==> q) <=> ~p \/ q` in
    let ptm = rand(concl pth) in
    let p_tm = rand(lhand ptm) and q_tm = rand ptm in
    fun th -> let ip,q = dest_comb(concl th) in
              let p = rand ip in
              EQ_MP (INST [p,p_tm; q,q_tm] pth) th
  and transform_iff_1 =
    let pth = UNDISCH(TAUT `(p <=> q) ==> (p \/ ~q)`) in
    let ptm = concl pth in
    let p_tm = lhand ptm and q_tm = rand(rand ptm) in
    fun th -> let ip,q = dest_comb(concl th) in
              let p = rand ip in
              PROVE_HYP th (INST [p,p_tm; q,q_tm] pth)
  and transform_iff_2 =
    let pth = UNDISCH(TAUT `(p <=> q) ==> (~p \/ q)`) in
    let ptm = concl pth in
    let p_tm = rand(lhand ptm) and q_tm = rand ptm in
    fun th -> let ip,q = dest_comb(concl th) in
              let p = rand ip in
              PROVE_HYP th (INST [p,p_tm; q,q_tm] pth) in
  let definitionalize th (n,tops,defs,lfn) =
    let t = concl th in
    if is_clausal t then
      let n',v,defs',lfn' = transvar (n,t,defs,lfn) in
      (n',(v,th)::tops,defs',lfn')
    else if is_neg t then
       let n1,v1,defs1,lfn1 = localdefs (rand t) (n,defs,lfn) in
       (n1,(mk_neg v1,th)::tops,defs1,lfn1)
    else if is_disj t then
      let n1,v1,defs1,lfn1 = localdefs (lhand t) (n,defs,lfn) in
      let n2,v2,defs2,lfn2 = localdefs (rand t) (n1,defs1,lfn1) in
      (n2,(mk_disj(v1,v2),th)::tops,defs2,lfn2)
    else if is_imp t then
      let n1,v1,defs1,lfn1 = localdefs (lhand t) (n,defs,lfn) in
      let n2,v2,defs2,lfn2 = localdefs (rand t) (n1,defs1,lfn1) in
      (n2,(mk_disj(mk_neg v1,v2),transform_imp th)::tops,defs2,lfn2)
    else if is_iff t then
      let n1,v1,defs1,lfn1 = localdefs (lhand t) (n,defs,lfn) in
      let n2,v2,defs2,lfn2 = localdefs (rand t) (n1,defs1,lfn1) in
      (n2,(mk_disj(v1,mk_neg v2),transform_iff_1 th)::
          (mk_disj(mk_neg v1,v2),transform_iff_2 th)::tops,defs2,lfn2)
    else
      let n',v,defs',lfn' = localdefs t (n,defs,lfn) in
      (n',(v,th)::tops,defs',lfn') in
  definitionalize;;

(* SAT_PROVE is the main interface function.
   Takes in a term t and returns thm or exception if not a taut *)
(* invokes minisatp, returns |- t  or |- model ==> ~t *)

(* if minisatp proof log does not exist after minisatp call returns,
   we will assume that minisatp discovered UNSAT during the read-in
   phase and did not bother with a proof log.
   In that case the problem is simple and can be delegated to TAUT *)

(* FIXME: I do not like the TAUT solution;
   what is trivial for Minisat may not be so for TAUT *)

exception Sat_counterexample of thm;;

(* delete temporary files *)
(* if zChaff was used, also delete hard-wired trace filenames*)
let CLEANUP fname solvername =
  let delete fname = try Sys.remove fname with Sys_error _ -> () in
  (delete fname;
   delete (fname^".cnf");
   delete (fname^"."^solvername);
   delete (fname^"."^solvername^".proof");
   delete (fname^"."^solvername^".stats");
   if solvername="zchaff" then
     (delete(Filename.concat (!temp_path) "resolve_trace");
      delete(Filename.concat (!temp_path) "zc2mso_trace"))
   else ());;

let GEN_SAT_PROVE solver solvername =
  let false_tm = `F`
  and presimp_conv = GEN_REWRITE_CONV DEPTH_CONV
   [NOT_CLAUSES; AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES]
  and p_tm = `p:bool` and q_tm = `q:bool`
  and pth_triv = TAUT `(~p <=> F) <=> p`
  and pth_main = UNDISCH_ALL(TAUT `(~p <=> q) ==> (q ==> F) ==> p`) in
  let triv_rule p th = EQ_MP(INST [p,p_tm] pth_triv) th
  and main_rule p q sth th =
    itlist PROVE_HYP [sth; DISCH_ALL th] (INST [p,p_tm; q,q_tm] pth_main) in
  let invoke_minisat lfn mcth stm t rcv vc =
    let nr = Array.length rcv in
    let res = match invokeSat solver None t (Some vc) with
      Some model ->
        let model2 =
          mapfilter (fun l -> let x = hd(frees l) in
                              let y = apply lfn x in
                              if is_var y then vsubst [y,x] l else fail())
                    model in
          satCheck model2 stm
    | None ->
      (match parseMinisatProof nr ((!tmp_name)^"."^solvername^".proof") vc rcv with
         Some (cl,sk,scl,srl,cc) ->
            unsatProveResolve lfn mcth (cl,sk,srl) (* returns p |- F *)
      | None -> UNDISCH(TAUT(mk_imp(stm,false_tm)))) in
    res in
  fun tm ->
    let sth = presimp_conv (mk_neg tm) in
    let stm = rand(concl sth) in
    if stm = false_tm then triv_rule tm sth else
    let th = ASSUME stm in
    let ths = if !exploit_conjunctive_structure then GCONJUNCTS th
              else [th] in
    let n,tops,defs,lfn =
      itlist definitionalize ths (-1,[],undefined,undefined) in
    let defg = foldl (fun a t nv -> (t,nv)::a) [] defs in
    let mdefs = filter (fun (r,_) -> not (is_var r)) defg in
    let eqs = map (fun (r,l) -> mk_iff(l,r)) mdefs in
    let clausify eq cls =
      let fvs = frees eq and eth = (NNFC_CONV THENC CNF_CONV) eq in
      let tth = INST (map (fun v -> apply lfn v,v) fvs) eth in
      let xth = ADD_ASSUM stm (EQ_MP tth (REFL(apply lfn (lhand eq)))) in
      zip (conjuncts(rand(concl eth))) (CONJUNCTS xth) @ cls in
    let all_clauses = itlist clausify eqs tops in
    let mcth = itlist (fun (c,th) m -> Termmap.add c th m) all_clauses
                      Termmap.empty in
    let vc = n + 1 in
    let rcv = Array.of_list (map fst all_clauses) in
    let ntdcnf = list_mk_conj (map fst all_clauses) in
    let th = invoke_minisat lfn mcth stm ntdcnf rcv vc in
    (if not (!sat_debugging) then CLEANUP (!tmp_name) solvername else ();
    if is_imp(concl th)
    then raise (Sat_counterexample
      (EQ_MP (AP_TERM (rator(concl th)) (SYM sth)) th))
    else main_rule tm stm sth th);;

let SAT_PROVE = GEN_SAT_PROVE minisatp "minisatp";;

let ZSAT_PROVE = GEN_SAT_PROVE zchaff "zchaff";;
