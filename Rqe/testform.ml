(* ====================================================================== *)
(*  TESTFORM                                                              *)
(* ====================================================================== *)

let rec TESTFORM var interpsigns_thm set_thm fm =
  let polys,set,signs = dest_interpsigns interpsigns_thm in
  let polys' = dest_list polys in
  let signs' = dest_list signs in
  if fm = t_tm then BETA_RULE (ISPECL [set] t_thm)
  else if fm = f_tm then BETA_RULE (ISPECL [set] f_thm)
  else if is_neg fm then
    let lam = mk_abs (var,dest_neg fm) in
    let thm = TESTFORM var interpsigns_thm set_thm (dest_neg fm) in
    if is_pos (concl thm) then
      MATCH_MP (BETA_RULE (ISPECL [lam;set] neg_thm_p)) thm
    else if is_neg (concl thm) then
      MATCH_MP (BETA_RULE (ISPECL [lam;set] neg_thm_n)) thm
    else failwith "error"
  else if is_conj fm then
    let a,b = dest_conj fm in
    let a',b' = mk_abs (var,a),mk_abs (var,b) in
    let thma = TESTFORM var interpsigns_thm set_thm a  in
    let thmb = TESTFORM var interpsigns_thm set_thm b  in
    if is_neg (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] and_thm_nn);set_thm;thma;thmb]
    else if is_neg (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] and_thm_np);set_thm;thma;thmb]
    else if is_pos (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] and_thm_pn);set_thm;thma;thmb]
    else if is_pos (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] and_thm_pp);set_thm;thma;thmb]
    else failwith "error"
  else if is_disj fm then
    let a,b = dest_disj fm in
    let a',b' = mk_abs (var,a),mk_abs (var,b) in
    let thma = TESTFORM var interpsigns_thm set_thm a  in
    let thmb = TESTFORM var interpsigns_thm set_thm b  in
    if is_neg (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] or_thm_nn);set_thm;thma;thmb]
    else if is_pos (concl thma) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] or_thm_p);set_thm;thma]
    else if is_pos (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] or_thm_q);set_thm;thmb]
    else failwith "error"
  else if is_imp fm then
    let a,b = dest_imp fm in
    let a',b' = mk_abs (var,a),mk_abs (var,b) in
    let thma = TESTFORM var interpsigns_thm set_thm a  in
    let thmb = TESTFORM var interpsigns_thm set_thm b  in
    if is_neg (concl thma) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] imp_thm_n);set_thm;thma]
    else if is_pos (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] imp_thm_pn);set_thm;thma;thmb]
    else if is_pos (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] imp_thm_pp);set_thm;thmb]
    else failwith "error"
  else if is_iff fm then
    let a,b = dest_eq fm in
    let a',b' = mk_abs (var,a),mk_abs (var,b) in
    let thma = TESTFORM var interpsigns_thm set_thm a  in
    let thmb = TESTFORM var interpsigns_thm set_thm b  in
    if is_neg (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] iff_thm_nn);set_thm;thma;thmb]
    else if is_neg (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] iff_thm_np);set_thm;thma;thmb]
    else if is_pos (concl thma) && is_neg (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] iff_thm_pn);set_thm;thma;thmb]
    else if is_pos (concl thma) && is_pos (concl thmb) then
      MATCH_MPL [BETA_RULE (ISPECL [a';b';set] iff_thm_pp);set_thm;thma;thmb]
    else failwith "error"
  else (* an atom *)
    let op,p,_ = get_binop fm in
    let lam = mk_abs (var,p) in
    let ind =
      try
        index lam polys'
      with Failure "index" -> failwith "TESTFORM: Poly not present in list" in
    let sign = ith ind signs' in
    let thm = ith ind (interpsigns_thms interpsigns_thm) in
    let thm_op,thm_p,_ =
      get_binop (snd (dest_imp (snd (dest_forall (concl thm))))) in
    if op = req then
      if thm_op = req then thm
      else if thm_op = rlt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] lt_eq_thm);thm]
      else if thm_op = rgt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] gt_eq_thm);thm]
      else failwith "error"
    else if op = rlt then
      if thm_op = rlt then thm
      else if  thm_op = req then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] eq_lt_thm);thm]
      else if thm_op = rgt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] gt_lt_thm);thm]
      else failwith "error"
    else if op = rgt then
      if thm_op = rgt then thm
      else if  thm_op = req then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] eq_gt_thm);thm]
      else if thm_op = rlt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] lt_gt_thm);thm]
      else failwith "error"
    else if op = rle then
      if thm_op = rlt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] lt_le_thm);thm]
      else if  thm_op = req then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] eq_le_thm);thm]
      else if thm_op = rgt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] gt_le_thm);thm]
      else failwith "error"
    else if op = rge then
      if thm_op = rlt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] lt_ge_thm);thm]
      else if  thm_op = req then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] eq_ge_thm);thm]
      else if thm_op = rgt then
        MATCH_MPL [BETA_RULE (ISPECL [lam;set] gt_ge_thm);thm]
      else failwith "error"
    else failwith "error" ;;

let TESTFORM var interpsigns_thm set_thm fm =
  let start_time = Sys.time() in
  let res = TESTFORM var interpsigns_thm set_thm fm in
    testform_timer +.= (Sys.time() -. start_time);
    res;;


let tvar,tmat,tfm = ref `T`,ref TRUTH,ref `T`;;
(*
let var,mat_thm,fm = !tvar,!tmat,!tfm
*)

let COMBINE_TESTFORMS =
  let lem1 = TAUT `(T ==> a) <=> a`
  and lem2 = TAUT `(T /\ x) <=> x`
  and imat_tm = `interpmat` in
  fun var mat_thm fm ->
  tvar := var;
  tmat := mat_thm;
  tfm := fm;
  (* if not (fst (strip_comb (concl mat_thm)) = imat_tm) then failwith "not a mat thm" else *)
  let mat_thm' = (CONV_RULE (RATOR_CONV (RAND_CONV (LIST_CONV (ALPHA_CONV var))))) mat_thm in
  let rol_thm,all2_thm = interpmat_thms mat_thm' in
  let ord_thms = rol_nonempty_thms rol_thm in
  let part_thm = PARTITION_LINE_CONV (snd(dest_comb(concl rol_thm))) in
  let isigns_thms = CONJUNCTS(REWRITE_RULE[ALL2;part_thm] all2_thm) in
  let ex_thms = map2 (fun x y -> TESTFORM var x y fm) isigns_thms ord_thms in
  if exists (fun x -> is_forall(concl x)) ex_thms then
    let witness_thm = find (fun x -> is_forall(concl x)) ex_thms in
    let i = try index witness_thm ex_thms with _ -> failwith "COMBINE_TESTFORMS: witness not present" in
    let ord_thm = ith i ord_thms in
    let x,bod = dest_exists (concl ord_thm) in
    if bod = t_tm then
      let thm1 = ISPEC var witness_thm in
      let thm2 = PURE_REWRITE_RULE[lem1] thm1 in
      let exists_thm = EXISTS (mk_exists(var,concl thm2),var) thm2 in
        EQT_INTRO exists_thm
    else
      let nv = new_var real_ty in
      let ord_thm' = CONV_RULE (RAND_CONV (ALPHA_CONV nv)) ord_thm in
      let y,bod = dest_exists (concl ord_thm') in
      let ass_thm = ASSUME bod in
      let thm = MATCH_MP witness_thm ass_thm in
      let exists_thm = EXISTS (mk_exists(y,concl thm) ,y) thm in
      let ret = CHOOSE (nv,ord_thm) exists_thm in
        EQT_INTRO ret
  else
    if length ord_thms = 1 && snd(dest_exists(concl (hd ord_thms))) = t_tm then
      PURE_REWRITE_RULE[lem2] (EQF_INTRO (hd ex_thms)) else
    let ex_thms' = map (MATCH_MP NOT_EXISTS_CONJ_THM) ex_thms in
    let len = length ex_thms' in
    let first,[t1;t2] = chop_list (len-2) ex_thms' in
    let base = MATCH_MPL[testform_itlem;t1;t2] in
    let ex_thm = itlist (fun x y -> MATCH_MPL[testform_itlem;x;y]) first base in
    let cover_thm = ROL_COVERS rol_thm in
    let pre_thm = MATCH_MP ex_thm (ISPEC var cover_thm) in
    let gen_thm = GEN var pre_thm in
    let ret = MATCH_EQ_MP FORALL_NOT_THM gen_thm in
      EQF_INTRO ret;;

let COMBINE_TESTFORMS var mat_thm fm =
  let start_time = Sys.time() in
  let res = COMBINE_TESTFORMS var mat_thm fm in
    combine_testforms_timer +.= (Sys.time() -. start_time);
    res;;

(* {{{ Examples *)
(*

let var,mat_thm,fm =
rx,ASSUME `interpsigns [\x. &1 + x * (&0 + x * &1)] (\x. T) [Pos]`,ASSUME `?x:real. T`


let ex_thms = map2 (fun x y -> TESTFORM var x y fm) isigns_thms ord_thms in
TESTFORM ry (hd isigns_thms) (hd ord_thms) fm
TESTFORM ry (hd isigns_thms) (hd ord_thms) `&1 + y * (&0 + x * -- &1) <= &0`
TESTFORM ry (hd isigns_thms) (hd ord_thms) `(&1 + x * (&0 + x * -- &1)) + y * (&0 + y * -- &1) < &0`
TESTFORM ry (hd isigns_thms) (hd ord_thms) `(&1 + y * (&0 + x * -- &1) <= &0) /\ (&1 + x * (&0 + x * -- &1)) + y * (&0 + y * -- &1) < &0`
let fm = `(&1 + y * (&0 + x * -- &1) <= &0) /\ (&1 + x * (&0 + x * -- &1)) + y * (&0 + y * -- &1) < &0`

let var,mat_thm,fm =
ry,
ASSUME `interpmat [] [\y. (&1 + x * (&0 + x * -- &1)) + y * (&0 + y * -- &1); \y. &1 + y * (&0 + x * -- &1)] [[Neg; Pos]]`,
`~((&1 + x * (&0 + x * -- &1)) + y * (&0 + y * -- &1) < &0 /\ &1 + y * (&0 + x * -- &1) <= &0)`

let var,mat_thm,fm =
ry,
ASSUME `interpmat [x_354]
        [\y. (&1 + x * -- &1) + y * (&0 + x * -- &2); \x. &1 + x * -- &1;
        \y. (&1 + x * -- &1) + y * (&0 + x * -- &2)]
        [[Neg; Pos; Neg]; [Neg; Zero; Neg]; [Neg; Neg; Neg]]`,
`~(&1 + x * -- &1 < &0 /\ &1 + y * -- &1 < &0
     ==> (&1 + x * -- &1) + y * (&0 + x * -- &2) < &0)`


*)

(* }}} *)
