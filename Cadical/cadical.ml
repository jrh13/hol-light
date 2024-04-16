(* ========================================================================= *)
(* Proving HOL tautologies via use of Cadical.                               *)
(* ========================================================================= *)

let cadical_debugging = ref false;;

let CADICAL_REFUTE_GEN amap tm =
  let cnfname = Filename.temp_file "cadicalhol" ".cnf"
  and lratname = Filename.temp_file "cadicalhol" ".lrat"
  and pratname = Filename.temp_file "cadicalhol" ".prat"
  and logname = Filename.temp_file "cadicalhol" ".log" in
  let _ = dimacs_of_hol cnfname tm in
  let command =
    "(cadical --no-binary --lrat "^cnfname^" "^pratname^"; "^
    "lrat-trim -a "^pratname^" "^lratname^"; "^
    "rm -f "^pratname^") >"^logname in
  let _ = Sys.command command in
  let res = LRAT_REFUTE_GEN amap cnfname lratname in
  let _ = if !cadical_debugging then 1 else Sys.command
          ("rm -f "^cnfname^" "^lratname^" "^logname) in
  res;;

let CADICAL_REFUTE =
  let false_tm = `F` in
  fun tm ->
    let aar = Array.of_list (false_tm::atoms tm) in
    let th = CADICAL_REFUTE_GEN (Array.get aar) tm in
    if hyp th = [tm] && concl th = false_tm then th
    else failwith "CADICAL_REFUTE: Sanity check failure";;

(* ------------------------------------------------------------------------- *)
(* General prover with definitional CNF built in                             *)
(* ------------------------------------------------------------------------- *)

let CADICAL_PROVE =
  let false_tm = `F`
  and p_tm = `p:bool` and q_tm = `q:bool`
  and pth_triv = TAUT `(~p <=> F) <=> p`
  and pth_main = UNDISCH_ALL(TAUT `(~p <=> q) ==> (q ==> F) ==> p`) in
  let presimp_conv = GEN_REWRITE_CONV DEPTH_CONV
    [NOT_CLAUSES; AND_CLAUSES; OR_CLAUSES; IMP_CLAUSES; EQ_CLAUSES]
  and triv_rule p th = EQ_MP(INST [p,p_tm] pth_triv) th
  and main_rule p q sth th =
    itlist PROVE_HYP [sth; DISCH_ALL th] (INST [p,p_tm; q,q_tm] pth_main) in
  fun tm ->
    if is_neg tm && is_strictcnf (rand tm) then
      NOT_INTRO(DISCH_ALL(CADICAL_REFUTE(rand tm)))
    else if is_imp tm && rand tm = false_tm && is_strictcnf (lhand tm) then
      DISCH_ALL(CADICAL_REFUTE(lhand tm))
    else
      let sth = presimp_conv(mk_neg tm) in
      let stm = rand(concl sth) in
      if stm = false_tm then triv_rule tm sth else
      let th = ASSUME stm in
      let ths = if !exploit_conjunctive_structure then GCONJUNCTS th
                else [th] in
      let n,tops,defs,lfn =
        itlist definitionalize ths (-1,[],undefined,undefined) in
      let defg = foldl (fun a t nv -> (t,nv)::a) [] defs in
      let mdefs = filter (fun (r,_) -> not (is_atom r)) defg in
      let eqs = map (fun (r,l) -> mk_iff(l,r)) mdefs in
      let clausify eq cls =
        let fvs = frees eq and eth = (NNFC_CONV THENC CNF_CONV) eq in
        let tth = INST (map (fun v -> apply lfn v,v) fvs) eth in
        let xth = ADD_ASSUM stm (EQ_MP tth (REFL(apply lfn (lhand eq)))) in
        zip (conjuncts(rand(concl eth))) (CONJUNCTS xth) @ cls in
      let all_clauses = itlist clausify eqs tops in
      let ntdcnf = list_mk_conj (map fst all_clauses) in
      let expat = map (apply lfn) (atoms ntdcnf) in
      let rar = Array.of_list(false_tm::expat) in
      let cth = CADICAL_REFUTE_GEN (Array.get rar) ntdcnf in
      let dth = PROVE_HYP (end_itlist CONJ (map snd all_clauses)) cth in
      let fth = main_rule tm stm sth dth in
      if concl fth = tm && hyp fth = [] then fth
      else failwith "CADICAL_PROVE: Sanity check";;
